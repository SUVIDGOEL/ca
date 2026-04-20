#include <immintrin.h>  
#include <openssl/aes.h>
#include <stdint.h>

#pragma GCC optimize("O3,unroll-loops")
#pragma GCC target("sse2,ssse3,bmi,bmi2")

#define AES_MAXNR 14
#define BLOCK_SIZE 16

/* ========= Same as OpenSSL AES_KEY_Custom ========= */
typedef struct {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
} AES_KEY_Custom;



static inline uint8_t gf_sq(uint8_t x) {
    // spread low 4 bits to even positions (bits 0,2,4,6)
    uint8_t r = (x & 1)        // b0 → bit 0
              | ((x & 2) << 1) // b1 → bit 2
              | ((x & 4) << 2) // b2 → bit 4
              | ((x & 8) << 3);// b3 → bit 6

    // XOR reduction polynomials for high bits b4,b5,b6,b7
    r ^= (-((x >> 4) & 1)) & 0x1B; // x^8  reduction
    r ^= (-((x >> 5) & 1)) & 0x6C; // x^10 reduction
    r ^= (-((x >> 6) & 1)) & 0xAB; // x^12 reduction
    r ^= (-((x >> 7) & 1)) & 0x9A; // x^14 reduction
    return r;
}

static inline uint8_t xtime(uint8_t x){  //multiplication by 2 in GF(2^8)
    return (x << 1) ^ (-((x>>7)&1) & 0x1b);
}

static inline uint8_t gf_mul(uint8_t a, uint8_t b){
    uint8_t res = 0;
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); b>>=1; a = xtime(a);
    res ^= a&(-(b&0x1)); 
    return res;
}

//Itoh-Tsuji Optimization
static inline uint8_t gf_inv(uint8_t x) {
    uint8_t x2   = gf_sq(x);          // x^2
    uint8_t x3   = gf_mul(x2, x);     // x^3
    uint8_t x6   = gf_sq(x3);         // x^6
    uint8_t x12  = gf_sq(x6);         // x^12
    uint8_t x14  = gf_mul(x12, x2);   // x^14
    uint8_t x15  = gf_mul(x12, x3);   // x^15
    uint8_t x30  = gf_sq(x15);        // x^30
    uint8_t x60  = gf_sq(x30);        // x^60
    uint8_t x120 = gf_sq(x60);        // x^120
    uint8_t x240 = gf_sq(x120);       // x^240
    return gf_mul(x240, x14);         // x^254
}

static inline uint8_t shift_left(uint8_t x, int n){ //circular shift to left
    return (x<<n)|(x>>(8-n));
}

//1. SubBytes Step

static inline uint8_t func_A(uint8_t x){ //function A
    return x^shift_left(x,1)^shift_left(x,2)^shift_left(x,3)^shift_left(x,4)^0x63;
}

static inline uint8_t sub_bytes(uint8_t x){ //Subbytes step for a byte
    return func_A(gf_inv(x));
}

static inline uint32_t sub_word(uint32_t x){
    return (uint32_t)sub_bytes(x & 0xFF)
         | ((uint32_t)sub_bytes((x >>  8) & 0xFF) <<  8)
         | ((uint32_t)sub_bytes((x >> 16) & 0xFF) << 16)
         | ((uint32_t)sub_bytes((x >> 24) & 0xFF) << 24);
}


//2. Shift Rows Step

//static inline __attribute__((always_inline)) void shift_rows(uint32_t* s){
//    uint32_t c0 = s[0];
//    uint32_t c1 = s[1];
//    uint32_t c2 = s[2];
//    uint32_t c3 = s[3];
    
//    s[0] = (c0 & 0x000000ff) | (c1 & 0x0000ff00) | (c2 & 0x00ff0000) | (c3 & 0xff000000);
//    s[1] = (c1 & 0x000000ff) | (c2 & 0x0000ff00) | (c3 & 0x00ff0000) | (c0 & 0xff000000);
//    s[2] = (c2 & 0x000000ff) | (c3 & 0x0000ff00) | (c0 & 0x00ff0000) | (c1 & 0xff000000);
//    s[3] = (c3 & 0x000000ff) | (c0 & 0x0000ff00) | (c1 & 0x00ff0000) | (c2 & 0xff000000);

//}

#define shift_rows_scalar(c0,c1,c2,c3) do { \
    uint32_t _t0,_t1,_t2,_t3;              \
    _t0=(c0&0x000000FF)|(c1&0x0000FF00)|(c2&0x00FF0000)|(c3&0xFF000000); \
    _t1=(c1&0x000000FF)|(c2&0x0000FF00)|(c3&0x00FF0000)|(c0&0xFF000000); \
    _t2=(c2&0x000000FF)|(c3&0x0000FF00)|(c0&0x00FF0000)|(c1&0xFF000000); \
    _t3=(c3&0x000000FF)|(c0&0x0000FF00)|(c1&0x00FF0000)|(c2&0xFF000000); \
    c0=_t0; c1=_t1; c2=_t2; c3=_t3;       \
} while(0)

//3.Mix Columns Step

static inline uint32_t mix_col(uint32_t w){
    uint8_t s0 =  w        & 0xFF;
    uint8_t s1 = (w >>  8) & 0xFF;
    uint8_t s2 = (w >> 16) & 0xFF;
    uint8_t s3 = (w >> 24) & 0xFF;

    uint8_t u  = s0 ^ s1 ^ s2 ^ s3;

    uint8_t n0 = s0 ^ u ^ xtime(s0 ^ s1);
    uint8_t n1 = s1 ^ u ^ xtime(s1 ^ s2);
    uint8_t n2 = s2 ^ u ^ xtime(s2 ^ s3);
    uint8_t n3 = s3 ^ u ^ xtime(s3 ^ s0);

    return (uint32_t)n0 | ((uint32_t)n1<<8) | ((uint32_t)n2<<16) | ((uint32_t)n3<<24);
}

//static inline __attribute__((always_inline)) void mix_columns(uint32_t s0, uint32_t s1, uint32_t s2, uint32_t s3){
//    s0 = mix_col(s0);
//    s1 = mix_col(s1);
//    s2 = mix_col(s2);
//    s3 = mix_col(s3);
//}

#define mix_columns_scalar(c0,c1,c2,c3) do { \
    c0=mix_col(c0); c1=mix_col(c1);          \
    c2=mix_col(c2); c3=mix_col(c3);          \
} while(0)


/* ========= AES Encryption ========= */

void AES_encrypt_custom(const unsigned char *plaintext,
                        unsigned char *ciphertext,
                        const AES_KEY_Custom *enc_key){

    //Write your code here (Note: Do not use ISA specific AES instruction that results in 0 marks)
        
    __m128i state_v = _mm_loadu_si128((const __m128i*)plaintext);
    __m128i key_v   = _mm_loadu_si128((const __m128i*)enc_key->rd_key);

    state_v = _mm_xor_si128(state_v, key_v);

    uint32_t s0 = _mm_extract_epi32(state_v, 0);
    uint32_t s1 = _mm_extract_epi32(state_v, 1);
    uint32_t s2 = _mm_extract_epi32(state_v, 2);
    uint32_t s3 = _mm_extract_epi32(state_v, 3);
    
    //1ST
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    __m128i r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[4]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
        
    //2ND
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[8]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //3RD
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[12]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);

    //4TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[16]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //5TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[20]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //6TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[24]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //7TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[28]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //8TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[32]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);
    
    //9TH
    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //3.Column Mix   Just implement the Column Fix Step
    mix_columns_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[36]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);


    //1. Sub Bytes
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    //2. Shift Rows
    shift_rows_scalar(s0,s1,s2,s3);

    //4.Add Round Key
    r_key = _mm_loadu_si128((const __m128i*)&enc_key->rd_key[40]);
    s0 ^= _mm_extract_epi32(r_key, 0);
    s1 ^= _mm_extract_epi32(r_key, 1);
    s2 ^= _mm_extract_epi32(r_key, 2);
    s3 ^= _mm_extract_epi32(r_key, 3);

    state_v = _mm_set_epi32(s3, s2, s1, s0);
    _mm_storeu_si128((__m128i*)ciphertext, state_v);

}

/* ========= Wrapper ========= */

void AES_code(unsigned char plaintext[16],
              unsigned char ciphertext[16],
              AES_KEY *enc_key)
{

    AES_encrypt_custom(plaintext, ciphertext, (AES_KEY_Custom *)enc_key); //Your AES code where there is no secret dependent memory access
    //AES_encrypt(plaintext, ciphertext, enc_key); //OpenSSL AES where there is secret dependent memory access
}
