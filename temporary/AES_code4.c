#define SIMDE_ENABLE_NATIVE_ALIASES
#include <simde/x86/sse2.h>
#include <simde/x86/ssse3.h>
#include <openssl/aes.h>
#include <stdint.h>

#pragma GCC optimize("O3")
#if defined(__x86_64__) || defined(__i386__)
#  pragma GCC target("sse2,ssse3")
#endif

#define mm_extract_epi32_sse2(v, i) \
    ((uint32_t)_mm_cvtsi128_si32(_mm_srli_si128((v), (i) * 4)))

#define AES_MAXNR 14
#define BLOCK_SIZE 16

typedef struct {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
} AES_KEY_Custom;

static inline __attribute__((always_inline)) uint32_t sub_word(uint32_t w) {
    uint32_t x, y, a1, a2, a3, a4, a5, a6;
    x = w;
    y = ((x & 0xFEFEFEFEu) >> 1) | ((x & 0x01010101u) << 7);
    x &= 0xDDDDDDDDu;
    x ^= y & 0x57575757u;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x1C1C1C1Cu;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x4A4A4A4Au;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x42424242u;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x64646464u;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0xE0E0E0E0u;
    a1 = x;
    a1 ^= (x & 0xF0F0F0F0u) >> 4;
    a2 = ((x & 0xCCCCCCCCu) >> 2) | ((x & 0x33333333u) << 2);
    a3 = x & a1;
    a3 ^= (a3 & 0xAAAAAAAAu) >> 1;
    a3 ^= (((x << 1) & a1) ^ ((a1 << 1) & x)) & 0xAAAAAAAAu;
    a4 = a2 & a1;
    a4 ^= (a4 & 0xAAAAAAAAu) >> 1;
    a4 ^= (((a2 << 1) & a1) ^ ((a1 << 1) & a2)) & 0xAAAAAAAAu;
    a5 = (a3 & 0xCCCCCCCCu) >> 2;
    a3 ^= ((a4 << 2) ^ a4) & 0xCCCCCCCCu;
    a4 = a5 & 0x22222222u;
    a4 |= a4 >> 1;
    a4 ^= (a5 << 1) & 0x22222222u;
    a3 ^= a4;
    a5 = a3 & 0xA0A0A0A0u;
    a5 |= a5 >> 1;
    a5 ^= (a3 << 1) & 0xA0A0A0A0u;
    a4 = a5 & 0xC0C0C0C0u;
    a6 = a4 >> 2;
    a4 ^= (a5 << 2) & 0xC0C0C0C0u;
    a5 = a6 & 0x20202020u;
    a5 |= a5 >> 1;
    a5 ^= (a6 << 1) & 0x20202020u;
    a4 |= a5;
    a3 ^= a4 >> 4;
    a3 &= 0x0F0F0F0Fu;
    a2 = a3;
    a2 ^= (a3 & 0x0C0C0C0Cu) >> 2;
    a4 = a3 & a2;
    a4 ^= (a4 & 0x0A0A0A0Au) >> 1;
    a4 ^= (((a3 << 1) & a2) ^ ((a2 << 1) & a3)) & 0x0A0A0A0Au;
    a5 = a4 & 0x08080808u;
    a5 |= a5 >> 1;
    a5 ^= (a4 << 1) & 0x08080808u;
    a4 ^= a5 >> 2;
    a4 &= 0x03030303u;
    a4 ^= (a4 & 0x02020202u) >> 1;
    a4 |= a4 << 2;
    a3 = a2 & a4;
    a3 ^= (a3 & 0x0A0A0A0Au) >> 1;
    a3 ^= (((a2 << 1) & a4) ^ ((a4 << 1) & a2)) & 0x0A0A0A0Au;
    a3 |= a3 << 4;
    a2 = ((a1 & 0xCCCCCCCCu) >> 2) | ((a1 & 0x33333333u) << 2);
    x = a1 & a3;
    x ^= (x & 0xAAAAAAAAu) >> 1;
    x ^= (((a1 << 1) & a3) ^ ((a3 << 1) & a1)) & 0xAAAAAAAAu;
    a4 = a2 & a3;
    a4 ^= (a4 & 0xAAAAAAAAu) >> 1;
    a4 ^= (((a2 << 1) & a3) ^ ((a3 << 1) & a2)) & 0xAAAAAAAAu;
    a5 = (x & 0xCCCCCCCCu) >> 2;
    x ^= ((a4 << 2) ^ a4) & 0xCCCCCCCCu;
    a4 = a5 & 0x22222222u;
    a4 |= a4 >> 1;
    a4 ^= (a5 << 1) & 0x22222222u;
    x ^= a4;
    y = ((x & 0xFEFEFEFEu) >> 1) | ((x & 0x01010101u) << 7);
    x &= 0x39393939u;
    x ^= y & 0x3F3F3F3Fu;
    y = ((y & 0xFCFCFCFCu) >> 2) | ((y & 0x03030303u) << 6);
    x ^= y & 0x97979797u;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x9B9B9B9Bu;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x3C3C3C3Cu;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0xDDDDDDDDu;
    y = ((y & 0xFEFEFEFEu) >> 1) | ((y & 0x01010101u) << 7);
    x ^= y & 0x72727272u;
    x ^= 0x63636363u;
    return x;
}

#define shift_rows_scalar(c0,c1,c2,c3) do { \
    uint32_t _t0,_t1,_t2,_t3;              \
    _t0=(c0&0x000000FF)|(c1&0x0000FF00)|(c2&0x00FF0000)|(c3&0xFF000000); \
    _t1=(c1&0x000000FF)|(c2&0x0000FF00)|(c3&0x00FF0000)|(c0&0xFF000000); \
    _t2=(c2&0x000000FF)|(c3&0x0000FF00)|(c0&0x00FF0000)|(c1&0xFF000000); \
    _t3=(c3&0x000000FF)|(c0&0x0000FF00)|(c1&0x00FF0000)|(c2&0xFF000000); \
    c0=_t0; c1=_t1; c2=_t2; c3=_t3;       \
} while(0)

static inline __attribute__((always_inline)) uint8_t xtime(uint8_t x){  
    return (x << 1) ^ (-((x>>7)&1) & 0x1b);
}

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

#define mix_columns_scalar(c0,c1,c2,c3) do { \
    c0=mix_col(c0); c1=mix_col(c1);          \
    c2=mix_col(c2); c3=mix_col(c3);          \
} while(0)


void AES_encrypt_custom(const unsigned char *plaintext,
                        unsigned char *ciphertext,
                        const AES_KEY_Custom *enc_key){
        
    __m128i state_v = _mm_loadu_si128((const __m128i*)plaintext);
    __m128i key_v   = _mm_loadu_si128((const __m128i*)enc_key->rd_key);

    state_v = _mm_xor_si128(state_v, key_v);

    uint32_t s0 = mm_extract_epi32_sse2(state_v, 0);
    uint32_t s1 = mm_extract_epi32_sse2(state_v, 1);
    uint32_t s2 = mm_extract_epi32_sse2(state_v, 2);
    uint32_t s3 = mm_extract_epi32_sse2(state_v, 3);
    
    // Rounds 1 through 9
    for(int i = 1; i <= 9; i++) {
        // 1. Sub Bytes
        s0 = sub_word(s0);
        s1 = sub_word(s1);
        s2 = sub_word(s2);
        s3 = sub_word(s3);

        // 2. Shift Rows
        shift_rows_scalar(s0, s1, s2, s3);

        // 3. Mix Columns
        mix_columns_scalar(s0, s1, s2, s3);

        // 4. Add Round Key
        s0 ^= enc_key->rd_key[i * 4 + 0];
        s1 ^= enc_key->rd_key[i * 4 + 1];
        s2 ^= enc_key->rd_key[i * 4 + 2];
        s3 ^= enc_key->rd_key[i * 4 + 3];
    }

    // Final Round 10 (No MixColumns)
    s0 = sub_word(s0);
    s1 = sub_word(s1);
    s2 = sub_word(s2);
    s3 = sub_word(s3);

    shift_rows_scalar(s0, s1, s2, s3);

    s0 ^= enc_key->rd_key[40];
    s1 ^= enc_key->rd_key[41];
    s2 ^= enc_key->rd_key[42];
    s3 ^= enc_key->rd_key[43];

    // Note: _mm_set_epi32 populates in reverse order (e3, e2, e1, e0)
    state_v = _mm_set_epi32(s3, s2, s1, s0);
    _mm_storeu_si128((__m128i*)ciphertext, state_v);
}

/* ====================================================================
   Wrapper
==================================================================== */
void AES_code(unsigned char plaintext[16],
              unsigned char ciphertext[16],
              AES_KEY *enc_key)
{
    // Execute custom, high-speed, constant-time AES
    AES_encrypt_custom(plaintext, ciphertext, (AES_KEY_Custom *)enc_key); 
}
