#include <stdint.h>
#include <string.h>

// Strictly O3. DO NOT unroll. Unrolling will cause the variables to overflow
// the 16 hardware registers, causing a catastrophic memory spill penalty.
#pragma GCC optimize("O3,unroll-loops,rename-registers,inline-functions")

#define AES_MAXNR 14

typedef struct {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
} AES_KEY_Custom;


/* ====================================================================
   64-bit Bitsliced S-Box (Register-Pinned Constant Math)
==================================================================== */
static inline __attribute__((always_inline)) uint64_t sub_u64(uint64_t w, uint64_t C01, uint64_t M_FE, uint64_t M_AA, uint64_t M_CC, uint64_t M_22) {
    uint64_t x, y, a1, a2, a3, a4, a5, a6;
    x = w;
    
    y = ((x & M_FE) >> 1) | ((x & C01) << 7);
    
    x &= (C01 * 0xDD); x ^= y & (C01 * 0x57);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x1C);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x4A);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x42);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x64);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0xE0);
    
    a1 = x; a1 ^= (x & (C01 * 0xF0)) >> 4;
    a2 = ((x & M_CC) >> 2) | ((x & (C01 * 0x33)) << 2);
    
    a3 = x & a1; a3 ^= (a3 & M_AA) >> 1;
    a3 ^= (((x << 1) & a1) ^ ((a1 << 1) & x)) & M_AA;
    a4 = a2 & a1; a4 ^= (a4 & M_AA) >> 1;
    a4 ^= (((a2 << 1) & a1) ^ ((a1 << 1) & a2)) & M_AA;
    a5 = (a3 & M_CC) >> 2; a3 ^= ((a4 << 2) ^ a4) & M_CC;
    a4 = a5 & M_22; a4 |= a4 >> 1; a4 ^= (a5 << 1) & M_22;
    a3 ^= a4; a5 = a3 & (C01 * 0xA0); a5 |= a5 >> 1; a5 ^= (a3 << 1) & (C01 * 0xA0);
    a4 = a5 & (C01 * 0xC0); a6 = a4 >> 2; a4 ^= (a5 << 2) & (C01 * 0xC0);
    a5 = a6 & (C01 * 0x20); a5 |= a5 >> 1; a5 ^= (a6 << 1) & (C01 * 0x20);
    a4 |= a5; a3 ^= a4 >> 4; a3 &= (C01 * 0x0F);
    
    a2 = a3; a2 ^= (a3 & (C01 * 0x0C)) >> 2;
    a4 = a3 & a2; a4 ^= (a4 & (C01 * 0x0A)) >> 1;
    a4 ^= (((a3 << 1) & a2) ^ ((a2 << 1) & a3)) & (C01 * 0x0A);
    a5 = a4 & (C01 * 0x08); a5 |= a5 >> 1; a5 ^= (a4 << 1) & (C01 * 0x08);
    a4 ^= a5 >> 2; a4 &= (C01 * 0x03);
    a4 ^= (a4 & (C01 * 0x02)) >> 1; a4 |= a4 << 2;
    a3 = a2 & a4; a3 ^= (a3 & (C01 * 0x0A)) >> 1;
    a3 ^= (((a2 << 1) & a4) ^ ((a4 << 1) & a2)) & (C01 * 0x0A);
    a3 |= a3 << 4; a2 = ((a1 & M_CC) >> 2) | ((a1 & (C01 * 0x33)) << 2);
    
    x = a1 & a3; x ^= (x & M_AA) >> 1;
    x ^= (((a1 << 1) & a3) ^ ((a3 << 1) & a1)) & M_AA;
    a4 = a2 & a3; a4 ^= (a4 & M_AA) >> 1;
    a4 ^= (((a2 << 1) & a3) ^ ((a3 << 1) & a2)) & M_AA;
    a5 = (x & M_CC) >> 2; x ^= ((a4 << 2) ^ a4) & M_CC;
    a4 = a5 & M_22; a4 |= a4 >> 1; a4 ^= (a5 << 1) & M_22;
    x ^= a4;
    
    y = ((x & M_FE) >> 1) | ((x & C01) << 7);
    x &= (C01 * 0x39); x ^= y & (C01 * 0x3F);
    y = ((y & (C01 * 0xFC)) >> 2) | ((y & (C01 * 0x03)) << 6);
    x ^= y & (C01 * 0x97);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x9B);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x3C);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0xDD);
    y = ((y & M_FE) >> 1) | ((y & C01) << 7);
    x ^= y & (C01 * 0x72);
    
    return x ^ (C01 * 0x63);
}

/* ====================================================================
   Pure 64-bit Matrix Math Macros (Avoids 32-bit splitting & spills)
==================================================================== */
// Cross-lane byte masking aligns the columns natively inside the 64-bit vars
#define SHIFT_ROWS_64(s0, s1) do { \
    uint64_t _v0 = (s0); \
    uint64_t _v1 = (s1); \
    (s0) = (_v0 & 0x000000FF000000FFull) | ((_v0 >> 32) & 0x000000000000FF00ull) | ((_v0 << 32) & 0xFF00000000000000ull) | \
           (_v1 & 0x00FF000000FF0000ull) | ((_v1 >> 32) & 0x00000000FF000000ull) | ((_v1 << 32) & 0x0000FF0000000000ull); \
    (s1) = (_v1 & 0x000000FF000000FFull) | ((_v1 >> 32) & 0x000000000000FF00ull) | ((_v1 << 32) & 0xFF00000000000000ull) | \
           (_v0 & 0x00FF000000FF0000ull) | ((_v0 >> 32) & 0x00000000FF000000ull) | ((_v0 << 32) & 0x0000FF0000000000ull); \
} while(0)

// Branchless, pure bitwise implementation processing 2 columns at once
static inline __attribute__((always_inline)) uint64_t mix_col_64(uint64_t w) {
    uint64_t mask = (uint64_t)((w & 0x8080808080808080ull) ^ 0x8080808080808080ull) >> 7;
    mask = ~mask; // Simulates arithmetic shift for multiplication
    
    uint64_t u = ((w << 1) & 0xFEFEFEFEFEFEFEFEull) ^ (mask & 0x1B1B1B1B1B1B1B1Bull);
    
    uint64_t r8  = (w >> 8)  | (w << 56);
    uint64_t r16 = (w >> 16) | (w << 48);
    uint64_t r24 = (w >> 24) | (w << 40);
    
    // Mask prevents logical blending across the 32-bit boundary within the 64-bit int
    return u ^ 
           ((r8 & 0x00FFFFFF00FFFFFFull) | ((w << 24) & 0xFF000000FF000000ull)) ^ 
           ((r16 & 0x0000FFFF0000FFFFull) | ((w << 16) & 0xFFFF0000FFFF0000ull)) ^ 
           ((r24 & 0x000000FF000000FFull) | ((w << 8)  & 0xFFFFFF00FFFFFF00ull));
}

/* ====================================================================
   Pure 64-bit AES Core
==================================================================== */
void AES_encrypt_custom(const unsigned char * __restrict__ plaintext,
                        unsigned char * __restrict__ ciphertext,
                        const AES_KEY_Custom * __restrict__ enc_key) {
    
    uint64_t s0, s1;
    const uint64_t *rk = (const uint64_t *)enc_key->rd_key;

    uint64_t C01 = 0x01010101;
    C01 |= (C01 << 32);
    
    uint64_t M_FE = C01 * 0xFE;
    uint64_t M_AA = C01 * 0xAA;
    uint64_t M_CC = C01 * 0xCC;
    uint64_t M_22 = C01 * 0x22;

    __builtin_memcpy(&s0, plaintext + 0, 8);
    __builtin_memcpy(&s1, plaintext + 8, 8);

    s0 ^= rk[0];
    s1 ^= rk[1];
    rk += 2; 

    for(int i = 1; i <= 9; i++) {
        // 1. S-Box (Native 64-bit)
        s0 = sub_u64(s0, C01, M_FE, M_AA, M_CC, M_22);
        s1 = sub_u64(s1, C01, M_FE, M_AA, M_CC, M_22);
        
        // 2. ShiftRows (Native 64-bit via macro)
        SHIFT_ROWS_64(s0, s1);
        
        // 3. MixColumns (Native 64-bit, 2 columns per cycle)
        s0 = mix_col_64(s0);
        s1 = mix_col_64(s1);
        
        // 4. Add Key
        s0 ^= rk[0];
        s1 ^= rk[1];
        rk += 2; 
    }

    // Final Round 10 (No MixColumns)
    s0 = sub_u64(s0, C01, M_FE, M_AA, M_CC, M_22);
    s1 = sub_u64(s1, C01, M_FE, M_AA, M_CC, M_22);

    SHIFT_ROWS_64(s0, s1);

    s0 ^= rk[0];
    s1 ^= rk[1];

    __builtin_memcpy(ciphertext + 0, &s0, 8);
    __builtin_memcpy(ciphertext + 8, &s1, 8);
}

void AES_code(unsigned char plaintext[16],
              unsigned char ciphertext[16],
              AES_KEY *enc_key)
{
    AES_encrypt_custom(plaintext, ciphertext, (AES_KEY_Custom *)enc_key); 
}
