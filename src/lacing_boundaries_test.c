/********************************************************************
 *                                                                  *
 * THIS FILE IS PART OF THE Ogg CONTAINER SOURCE CODE.              *
 * USE, DISTRIBUTION AND REPRODUCTION OF THIS LIBRARY SOURCE IS     *
 * GOVERNED BY A BSD-STYLE SOURCE LICENSE INCLUDED WITH THIS SOURCE *
 * IN 'COPYING'. PLEASE READ THESE TERMS BEFORE DISTRIBUTING.       *
 *                                                                  *
 ********************************************************************

  Regression test for the Ogg page/lacing 255-segment boundary and
  for large packets spanning multiple pages.

  The test encodes packets through the public libogg framing API and
  then validates the emitted bitstream against the public Ogg page
  format (RFC 3533) using an independent validator written for this
  test: it does not call any libogg routine to interpret pages, it
  parses the capture pattern, header, segment table and CRC itself,
  and reconstructs packet boundaries purely from the lacing rule
  (a run of 255 values continues a packet, the first value < 255
  terminates it).  The reconstructed packets are compared byte for
  byte with the encoder input.

  Constraints asserted on every produced page:
    * number_page_segments is in [1,255]
    * every lacing value is in [0,255]
    * the body length equals the sum of the lacing values
    * the header/body CRC matches an independently computed CRC-32
    * the continuation flag matches whether a packet is left open
      across the page boundary
    * packet boundaries and content are lossless.
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ogg/ogg.h>

/* ---- independent RFC 3533 CRC-32 (poly 0x04c11db7, init/final 0) ---- */
static ogg_uint32_t crc_tab[256];
static void crc_init(void){
  for(unsigned i=0;i<256;i++){
    ogg_uint32_t r=i<<24;
    for(int j=0;j<8;j++)
      r=(r&0x80000000u)?((r<<1)^0x04c11db7u):(r<<1);
    crc_tab[i]=r;
  }
}
static unsigned char patbyte(long pkt,long pos){
  return (unsigned char)((pkt*131+pos*7+17)&0xff);
}

static int fail(const char*what){
  fprintf(stderr,"FAIL: %s\n",what);
  return 1;
}

/* Independent validation of a complete bitstream.
 * sizes[]/npack describe the packets that were encoded. */
static int validate_stream(const unsigned char*blob,long blob_len,
                           const long long*sizes,int npack){
  long off=0;
  int page_no=0;
  int saw254=0,saw255=0;
  int open_packet=0;          /* a 255-run left a packet unclosed */
  long long pkt_idx=0;        /* reconstructed packet index */
  unsigned char*cur=NULL;     /* open packet accumulator */
  long cur_len=0,cur_cap=0;

  while(off<blob_len){
    if(blob_len-off<27) return fail("truncated fixed header");
    if(memcmp(blob+off,"OggS",4)) return fail("capture pattern");
    const unsigned char*h=blob+off;
    int version=h[4], flags=h[5], nseg=h[26];
    if(version!=0) return fail("version");
    if(nseg<1||nseg>255) return fail("segment count out of range");
    if(nseg==254)saw254=1;
    if(nseg==255)saw255=1;
    long hlen=27+nseg;
    if(blob_len-off<hlen) return fail("truncated segment table");

    long body_len=0;
    for(int k=0;k<nseg;k++){
      int v=h[27+k];
      if(v<0||v>255) return fail("lacing value out of range");
      body_len+=v;
    }
    if(blob_len-off<hlen+body_len) return fail("truncated body");
    const unsigned char*body=blob+off+hlen;

    /* CRC: stored field is zeroed for the computation. */
    unsigned char hcopy[27+255];
    memcpy(hcopy,h,(size_t)hlen);
    memset(hcopy+22,0,4);
    ogg_uint32_t stored=(ogg_uint32_t)h[22]|((ogg_uint32_t)h[23]<<8)|
                        ((ogg_uint32_t)h[24]<<16)|((ogg_uint32_t)h[25]<<24);
    ogg_uint32_t crc=0;
    for(long i=0;i<hlen;i++)
      crc=(crc<<8)^crc_tab[((crc>>24)&0xff)^hcopy[i]];
    for(long i=0;i<body_len;i++)
      crc=(crc<<8)^crc_tab[((crc>>24)&0xff)^body[i]];
    if(stored!=crc) return fail("CRC mismatch");

    int continued=flags&0x01;
    int bos=flags&0x02;
    if(page_no==0){ if(!bos) return fail("first page missing BOS"); }
    else if(bos) return fail("BOS flag after first page");
    if(continued!=open_packet) return fail("continuation flag mismatch");

    /* walk segments, reconstruct packets purely from lacing */
    long bpos=0;
    for(int k=0;k<nseg;k++){
      int v=h[27+k];
      if(!cur){
        cur_cap=v? (long)v:64;
        cur=malloc((size_t)cur_cap);
        cur_len=0;
      }
      if(cur_len+v>cur_cap){
        while(cur_len+v>cur_cap) cur_cap*=2;
        cur=realloc(cur,(size_t)cur_cap);
      }
      memcpy(cur+cur_len,body+bpos,(size_t)v);
      cur_len+=v; bpos+=v;
      if(v<255){
        /* packet terminates here */
        if(pkt_idx>=npack) return fail("too many reconstructed packets");
        if(cur_len!=(long)sizes[pkt_idx]){
          fprintf(stderr,"packet %lld size %ld != expected %lld\n",
                  pkt_idx,cur_len,sizes[pkt_idx]);
          return fail("reconstructed packet size");
        }
        for(long j=0;j<cur_len;j++)
          if(cur[j]!=patbyte(pkt_idx,j))
            return fail("reconstructed packet content");
        free(cur); cur=NULL; cur_len=cur_cap=0;
        open_packet=0;
        pkt_idx++;
      }else{
        open_packet=1;
      }
    }
    if(bpos!=body_len) return fail("segment walk length");
    off+=hlen+body_len;
    page_no++;
  }
  if(open_packet) return fail("unterminated packet at end of stream");
  if(pkt_idx!=npack) return fail("reconstructed packet count");
  if(!saw255) return fail("test never produced a 255-segment page");
  fprintf(stderr,"  independent validator: %d pages, 255-seg pages %s, "
                 "254-seg pages %s\n",
          page_no, saw255?"present":"absent",
          saw254?"present":"absent");
  return 0;
}

/* Encode packets with a chosen flush policy and validate the result.
 * policy: 0 = natural pageout + final flush
 *         1 = forced flush after every packet
 *         2 = submit the whole backlog first, then a single final flush
 * use_iovec: when nonzero, submit each packet through ogg_stream_iovecin
 *         split into fragments deliberately misaligned with the 255-byte
 *         segment size (fragments of 100/130/remainder), so one logical
 *         packet spans several iov entries and several segments. */
static int run_case(const long long*sizes,int npack,int policy,
                    int require254,int use_iovec){
  long long total=0;
  for(int i=0;i<npack;i++) total+=sizes[i];
  unsigned char*src=malloc((size_t)total?(size_t)total:1);
  long long p=0;
  for(int i=0;i<npack;i++)
    for(long long j=0;j<sizes[i];j++) src[p++]=patbyte(i,j);

  ogg_stream_state os;
  if(ogg_stream_init(&os,0x04030201)) return fail("ogg_stream_init");

  /* generous output buffer: one 282-byte header per lacing value max */
  long long max_lacing=0;
  for(int i=0;i<npack;i++) max_lacing+=sizes[i]/255+1;
  size_t cap=(size_t)total+(size_t)(max_lacing+1)*282+64;
  unsigned char*out=malloc(cap);
  long fill=0;

  p=0;
  for(int i=0;i<npack;i++){
    long long plen=sizes[i];
    if(use_iovec){
      /* split into <=4 fragments at offsets unrelated to 255 */
      ogg_iovec_t iov[4]; int ni=0; long long done=0;
      static const long long cut[]={100,130,90};
      for(int f=0; f<3 && done<plen; f++){
        long long fr=plen-done;
        if(fr>cut[f]) fr=cut[f];
        iov[ni].iov_base=src+p+done;
        iov[ni].iov_len=(size_t)fr;
        done+=fr; ni++;
      }
      if(done<plen){
        iov[ni].iov_base=src+p+done;
        iov[ni].iov_len=(size_t)(plen-done);
        ni++;
      }
      if(ogg_stream_iovecin(&os,iov,ni,(i==npack-1),
                            (ogg_int64_t)(i+1)*1000))
        return fail("iovecin");
    }else{
      ogg_packet op;
      memset(&op,0,sizeof(op));
      op.packet=src+p;
      op.bytes=(long)plen;
      if((long long)op.bytes!=plen) return fail("size exceeds long");
      op.b_o_s=(i==0);
      op.e_o_s=(i==npack-1);
      op.granulepos=(ogg_int64_t)(i+1)*1000;
      if(ogg_stream_packetin(&os,&op)) return fail("packetin");
    }
    p+=plen;

    ogg_page og;
    if(policy==1){
      while(ogg_stream_flush(&os,&og)){
        memcpy(out+fill,og.header,og.header_len); fill+=og.header_len;
        memcpy(out+fill,og.body,og.body_len);     fill+=og.body_len;
      }
    }else if(policy==0){
      while(ogg_stream_pageout(&os,&og)){
        memcpy(out+fill,og.header,og.header_len); fill+=og.header_len;
        memcpy(out+fill,og.body,og.body_len);     fill+=og.body_len;
      }
    }
    /* policy 2: no intermediate flush; build the full backlog. */
  }
  ogg_page og;
  while((policy==2)?ogg_stream_flush_fill(&os,&og,1L<<30)
                  :ogg_stream_flush(&os,&og)){
    memcpy(out+fill,og.header,og.header_len); fill+=og.header_len;
    memcpy(out+fill,og.body,og.body_len);     fill+=og.body_len;
  }

  /* public-API round-trip through sync/stream */
  ogg_sync_state oy; ogg_sync_init(&oy);
  ogg_stream_state ds; ogg_stream_init(&ds,0x04030201);
  long off=0; int got=0; long long coff=0;
  while(off<fill){
    long c=4096; if(c>fill-off)c=fill-off;
    char*b=ogg_sync_buffer(&oy,c);
    memcpy(b,out+off,(size_t)c); ogg_sync_wrote(&oy,c); off+=c;
    ogg_page pg; int r;
    while((r=ogg_sync_pageout(&oy,&pg))!=0){
      if(r<0) continue;
      if(ogg_stream_pagein(&ds,&pg)) return fail("pagein");
      ogg_packet dec;
      while(ogg_stream_packetout(&ds,&dec)==1){
        if(got>=npack) return fail("too many decoded packets");
        if((long long)dec.bytes!=sizes[got]) return fail("decoded size");
        if(memcmp(dec.packet,src+coff,(size_t)dec.bytes))
          return fail("decoded content");
        coff+=dec.bytes; got++;
      }
    }
  }
  if(got!=npack||coff!=total) return fail("decoded count/bytes");

  /* independent bitstream validation */
  if(validate_stream(out,fill,sizes,npack)){
    fprintf(stderr,"  (case policy=%d)\n",policy);
    return 1;
  }
  if(require254){
    /* confirm a 254-segment page exists by direct scan */
    long q=0; int has=0;
    while(q<fill){ int ns=out[q+26]; if(ns==254)has=1;
      long bl=0; for(int k=0;k<ns;k++)bl+=out[q+27+k]; q+=27+ns+bl; }
    if(!has) return fail("required 254-segment page not produced");
  }

  ogg_stream_clear(&os); ogg_stream_clear(&ds); ogg_sync_clear(&oy);
  free(src); free(out);
  return 0;
}

int main(void){
  crc_init();

  /* (a) the acceptance size sequence, including 255*255 and 255^3. */
  {
    long long s[]={254,255,256,510,
                   255LL*255-1,255LL*255,255LL*255+1,
                   255LL*255*255};
    int n=(int)(sizeof(s)/sizeof(s[0]));
    fprintf(stderr,"test (a) acceptance sizes, natural pageout\n");
    if(run_case(s,n,0,0,0)) return 1;
    fprintf(stderr,"test (a) acceptance sizes, forced flush\n");
    if(run_case(s,n,1,0,0)) return 1;
  }

  /* (b) packets whose lacing count is exactly 255 and exactly 254,
   * flushed individually so each lands on its own page. */
  {
    /* 65024 = 254*255+254 -> 255 segments;
     * 64769 = 253*255+254 -> 254 segments;
     * 65025 = 255*255     -> 256 segments (spans pages, 0 terminator) */
    long long s[]={254,65024,64769,255,256,65025};
    int n=(int)(sizeof(s)/sizeof(s[0]));
    fprintf(stderr,"test (b) exact 254/255 segment pages\n");
    if(run_case(s,n,1,1,0)) return 1;
  }

  /* (c) boundary stress: many small packets that fill pages to the
   * 255-segment cap, interleaved with nil (0-lacing) packets. */
  {
    int n=600;
    long long*s=malloc(sizeof(long long)*(size_t)n);
    for(int i=0;i<n;i++){
      if(i%50==49) s[i]=0;                 /* periodic nil packet */
      else if(i%7==0) s[i]=255;            /* one full segment + 0 */
      else s[i]=(i%253)+1;                 /* 1..253 -> one segment */
    }
    fprintf(stderr,"test (c) small/nil packet 255-segment fill\n");
    /* backlog then a single drain packs buffered one-segment packets
     * into full 255-segment pages (natural pageout waits for 4096 bytes
     * and per-packet flush would isolate every packet). */
    int rc=run_case(s,n,2,0,0);
    free(s);
    if(rc) return 1;
  }

  /* (d) back-to-back oversized packets that each span whole pages. */
  {
    long long s[]={65025,65025,65026,65024,130050,37};
    int n=(int)(sizeof(s)/sizeof(s[0]));
    fprintf(stderr,"test (d) back-to-back oversized packets\n");
    if(run_case(s,n,0,0,0)) return 1;
  }

  /* (e) boundary sizes delivered through ogg_stream_iovecin, each
   * packet split into fragments misaligned with the 255-byte segment
   * boundaries (all non-nil; a nil iovec has no fragments to split). */
  {
    long long s[]={254,255,256,510,100,65024,65025,65026,130050,7};
    int n=(int)(sizeof(s)/sizeof(s[0]));
    fprintf(stderr,"test (e) fragmented iovec packets across segments\n");
    if(run_case(s,n,0,0,1)) return 1;
    if(run_case(s,n,1,0,1)) return 1;
  }

  fprintf(stderr,"all lacing boundary tests passed\n");
  return 0;
}
