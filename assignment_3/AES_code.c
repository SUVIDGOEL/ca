#include <openssl/aes.h>
#include <stdint.h>

#pragma GCC optimize("O3,unroll-loops")
#pragma GCC target("bmi,bmi2")

#define AES_MAXNR 14
#define BLOCK_SIZE 16

/* ========= Same as OpenSSL AES_KEY_Custom ========= */
typedef struct {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
} AES_KEY_Custom;



static inline __attribute__((always_inline)) uint8_t gf_sq(uint8_t x) {
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

static inline __attribute__((always_inline)) uint8_t xtime(uint8_t x){  //multiplication by 2 in GF(2^8)
    return (x << 1) ^ (-((x>>7)&1) & 0x1b);
}

static inline __attribute__((always_inline)) uint8_t gf_mul(uint8_t a, uint8_t b){
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

static inline __attribute__((always_inline)) uint8_t gf_inv(uint8_t x) {
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

static inline __attribute__((always_inline)) uint8_t shift_left(uint8_t x, int n){ //circular shift to left
    return (x<<n)|(x>>(8-n));
}

//1. SubBytes Step

static inline __attribute__((always_inline)) uint8_t func_A(uint8_t x){ //function A
    return x^shift_left(x,1)^shift_left(x,2)^shift_left(x,3)^shift_left(x,4)^0x63;
}

static inline __attribute__((always_inline)) uint8_t sub_bytes(uint8_t x){ //Subbytes step for a byte
    return func_A(gf_inv(x));
}

static inline __attribute__((always_inline)) uint32_t sub_word(uint32_t x){
    return (uint32_t)sub_bytes(x & 0xFF)
         | ((uint32_t)sub_bytes((x >>  8) & 0xFF) <<  8)
         | ((uint32_t)sub_bytes((x >> 16) & 0xFF) << 16)
         | ((uint32_t)sub_bytes((x >> 24) & 0xFF) << 24);
}


//2. Shift Rows Step

static inline __attribute__((always_inline)) void shift_rows(uint32_t* s){
    uint32_t c0 = s[0];
    uint32_t c1 = s[1];
    uint32_t c2 = s[2];
    uint32_t c3 = s[3];
    
    s[0] = (c0 & 0x000000ff) | (c1 & 0x0000ff00) | (c2 & 0x00ff0000) | (c3 & 0xff000000);
    s[1] = (c1 & 0x000000ff) | (c2 & 0x0000ff00) | (c3 & 0x00ff0000) | (c0 & 0xff000000);
    s[2] = (c2 & 0x000000ff) | (c3 & 0x0000ff00) | (c0 & 0x00ff0000) | (c1 & 0xff000000);
    s[3] = (c3 & 0x000000ff) | (c0 & 0x0000ff00) | (c1 & 0x00ff0000) | (c2 & 0xff000000);

}

//3.Mix Columns Step

static inline __attribute__((always_inline)) uint32_t mix_col(uint32_t w){
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

static inline __attribute__((always_inline)) void mix_columns(uint32_t s[4]){
    s[0] = mix_col(s[0]);
    s[1] = mix_col(s[1]);
    s[2] = mix_col(s[2]);
    s[3] = mix_col(s[3]);
}


/* ========= AES Encryption ========= */

void AES_encrypt_custom(const unsigned char *plaintext,
                        unsigned char *ciphertext,
                        const AES_KEY_Custom *enc_key){

    //Write your code here (Note: Do not use ISA specific AES instruction that results in 0 marks)
        

    uint32_t s[4];
    s[0] = ((uint32_t)plaintext[0] | (uint32_t)plaintext[1]<<8 | (uint32_t)plaintext[2]<<16 | (uint32_t)plaintext[3]<<24);
    s[1] = ((uint32_t)plaintext[4] | (uint32_t)plaintext[5]<<8 | (uint32_t)plaintext[6]<<16 | (uint32_t)plaintext[7]<<24);
    s[2] = ((uint32_t)plaintext[8] | (uint32_t)plaintext[9]<<8 | (uint32_t)plaintext[10]<<16 | (uint32_t)plaintext[11]<<24);
    s[3] = ((uint32_t)plaintext[12] | (uint32_t)plaintext[13]<<8 | (uint32_t)plaintext[14]<<16 | (uint32_t)plaintext[15]<<24);
  
    s[0] = s[0]^(enc_key->rd_key[0]);
    s[1] = s[1]^(enc_key->rd_key[1]);
    s[2] = s[2]^(enc_key->rd_key[2]);
    s[3] = s[3]^(enc_key->rd_key[3]);
    
    for(int i=1;i<=9;i++){
        //1. Sub Bytes
        s[0] = sub_word(s[0]);
        s[1] = sub_word(s[1]);
        s[2] = sub_word(s[2]);
        s[3] = sub_word(s[3]);

        //2. Shift Rows
        shift_rows(s);

        //3.Column Mix   Just implement the Column Fix Step
        mix_columns(s);

        //4.Add Round Key
        
        s[0] ^= enc_key->rd_key[(i<<2)^0];
        s[1] ^= enc_key->rd_key[(i<<2)^1];
        s[2] ^= enc_key->rd_key[(i<<2)^2];
        s[3] ^= enc_key->rd_key[(i<<2)^3];
        
    }

    //1. Sub Bytes
    s[0] = sub_word(s[0]);
    s[1] = sub_word(s[1]);
    s[2] = sub_word(s[2]);
    s[3] = sub_word(s[3]);

    //2. Shift Rows
    shift_rows(s);

    //4.Add Round Key 
    s[0] ^= enc_key->rd_key[40];
    s[1] ^= enc_key->rd_key[41];
    s[2] ^= enc_key->rd_key[42];
    s[3] ^= enc_key->rd_key[43];


    uint32_t *dest = (uint32_t *)ciphertext;
    dest[0] = s[0];
    dest[1] = s[1];
    dest[2] = s[2];
    dest[3] = s[3];

}

/* ========= Wrapper ========= */

void AES_code(unsigned char plaintext[16],
              unsigned char ciphertext[16],
              AES_KEY *enc_key)
{

    AES_encrypt_custom(plaintext, ciphertext, (AES_KEY_Custom *)enc_key); //Your AES code where there is no secret dependent memory access
    //AES_encrypt(plaintext, ciphertext, enc_key); //OpenSSL AES where there is secret dependent memory access
}
