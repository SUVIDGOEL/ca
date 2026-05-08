#include <stdint.h>
#include <string.h>
#include <openssl/aes.h>

#pragma GCC optimize("O3,unroll-loops")

#define AES_MAXNR 14
#define BLOCK_SIZE 16 

typedef struct {
    unsigned int rd_key[4 * (AES_MAXNR + 1)];
    int rounds;
} AES_KEY_Custom;

/* ====================================================================
   64-bit Bitsliced S-Box (Register-Pinned Constant Math)
==================================================================== */
// We pass the pinned masks directly. The compiler will hold these in r8-r13.
static inline __attribute__((always_inline)) uint64_t sub_u64(uint64_t w, uint64_t C01, uint64_t M_FE, uint64_t M_AA, uint64_t M_CC, uint64_t M_22) {
    uint64_t x, y, a1, a2, a3, a4, a5, a6;
    x = w;
    
    // Core Rotation
    y = ((x & M_FE) >> 1) | ((x & C01) << 7);
    
    // Dynamic multiplication is only used for the rare constants now
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
    
    // Pinned masks (M_AA, M_CC, M_22) eliminate dozens of ALU multiplication cycles
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
   32-bit Matrix Math Macros (Exploits 32-bit hardware Immediates)
==================================================================== */
#define shift_rows_scalar(c0,c1,c2,c3) do { \
    uint32_t _t0 = (c0 & 0x000000FF) | (c1 & 0x0000FF00) | (c2 & 0x00FF0000) | (c3 & 0xFF000000); \
    uint32_t _t1 = (c1 & 0x000000FF) | (c2 & 0x0000FF00) | (c3 & 0x00FF0000) | (c0 & 0xFF000000); \
    uint32_t _t2 = (c2 & 0x000000FF) | (c3 & 0x0000FF00) | (c0 & 0x00FF0000) | (c1 & 0xFF000000); \
    uint32_t _t3 = (c3 & 0x000000FF) | (c0 & 0x0000FF00) | (c1 & 0x00FF0000) | (c2 & 0xFF000000); \
    c0 = _t0; c1 = _t1; c2 = _t2; c3 = _t3; \
} while(0)

// Natively compiles to x86 'ror' (1 cycle)
#define ROR32(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

static inline __attribute__((always_inline)) uint32_t mix_col_32(uint32_t w) {
    uint32_t msb = w & 0x80808080u;
    uint32_t u = ((w << 1) & 0xFEFEFEFEu) ^ ((msb >> 7) * 0x1Bu);
    return u ^ ROR32(w ^ u, 8) ^ ROR32(w, 16) ^ ROR32(w, 24);
}

/* ====================================================================
   Hybrid 64/32-bit AES Core
==================================================================== */
void AES_encrypt_custom(const unsigned char * __restrict__ plaintext,
                        unsigned char * __restrict__ ciphertext,
                        const AES_KEY_Custom * __restrict__ enc_key) {
    
    uint64_t s0, s1;
    const uint64_t *rk = (const uint64_t *)enc_key->rd_key;
    //const uint64_t *rk = (const uint64_t *)enc_key->rd_key;

    // Build the base 64-bit constant. 
    uint64_t C01 = 0x01010101;
    C01 |= (C01 << 32);
    
    // PIN THE HEAVY MASKS: The compiler will hold these in native registers.
    // This entirely deletes hundreds of ALU multiplication cycles from the S-Box.
    uint64_t M_FE = C01 * 0xFE;
    uint64_t M_AA = C01 * 0xAA;
    uint64_t M_CC = C01 * 0xCC;
    uint64_t M_22 = C01 * 0x22;

    // Load 16 bytes directly into two 64-bit integer registers
    __builtin_memcpy(&s0, plaintext + 0, 8);
    __builtin_memcpy(&s1, plaintext + 8, 8);

   
    s0^=rk[0];
    s1^=rk[1];
    rk += 2; // Pointer chasing skips ALU math (i * 2)

    for(int i = 1; i <= 9; i++) {
        // 1. S-Box: Runs at 64-bit speed using the Pinned Masks
        s0 = sub_u64(s0, C01, M_FE, M_AA, M_CC, M_22);
        s1 = sub_u64(s1, C01, M_FE, M_AA, M_CC, M_22);
        
        // 2. Split state into four 32-bit columns natively (0 cycles, logical split)
        uint32_t c0 = (uint32_t)s0;
        uint32_t c1 = (uint32_t)(s0 >> 32);
        uint32_t c2 = (uint32_t)s1;
        uint32_t c3 = (uint32_t)(s1 >> 32);
        
        // 3. Matrix Math: 32-bit alignment leverages 32-bit hardware immediates natively
        shift_rows_scalar(c0, c1, c2, c3);
        
        c0 = mix_col_32(c0);
        c1 = mix_col_32(c1);
        c2 = mix_col_32(c2);
        c3 = mix_col_32(c3);
       
        // 4. Recombine into 64-bit and Add Key
        s0 = ((uint64_t)c0) | (((uint64_t)c1) << 32);
        s1 = ((uint64_t)c2) | (((uint64_t)c3) << 32);


	s0^=rk[0];
	s1^=rk[1];
        rk += 2; // Chase pointer
    }

    // Final Round 10 (No MixColumns)
    s0 = sub_u64(s0, C01, M_FE, M_AA, M_CC, M_22);
    s1 = sub_u64(s1, C01, M_FE, M_AA, M_CC, M_22);

    uint32_t c0 = (uint32_t)s0;
    uint32_t c1 = (uint32_t)(s0 >> 32);
    uint32_t c2 = (uint32_t)s1;
    uint32_t c3 = (uint32_t)(s1 >> 32);

    shift_rows_scalar(c0, c1, c2, c3);

    s0 = ((uint64_t)c0) | (((uint64_t)c1) << 32);
    s1 = ((uint64_t)c2) | (((uint64_t)c3) << 32);

    s0^=rk[0];
    s1^=rk[1];

    // Safely write out results
    __builtin_memcpy(ciphertext + 0, &s0, 8);
    __builtin_memcpy(ciphertext + 8, &s1, 8);
}

void AES_code(unsigned char plaintext[16],
              unsigned char ciphertext[16],
              AES_KEY *enc_key)
{

    AES_encrypt_custom(plaintext, ciphertext, (AES_KEY_Custom *)enc_key); //Your AES code where there is no secret dependent memory access
    //AES_encrypt(plaintext, ciphertext, enc_key); //OpenSSL AES where there is secret dependent memory access
}
