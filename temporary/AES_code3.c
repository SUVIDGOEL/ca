#pragma GCC optimize("O3,unroll-loops")
#pragma GCC target("no-aes,ssse3")
#include <openssl/aes.h>
#include <stdint.h>
#include <string.h>
#include <immintrin.h>
#define AES_MAXNR 14
typedef struct { unsigned int rd_key[4*(AES_MAXNR+1)]; int rounds; } AES_KEY_Custom;

/* ================================================================
 * SIMD GF(2^8) arithmetic — all 16 bytes in parallel
 * ================================================================ */

#define Z   _mm_setzero_si128()
#define SB1 _mm_set1_epi8((int8_t)0x1b)

/* xtime: multiply 16 bytes by x in GF(2^8) */
static __attribute__((always_inline)) inline __m128i xtv(__m128i a) {
    return _mm_xor_si128(_mm_add_epi8(a,a),
                         _mm_and_si128(_mm_cmpgt_epi8(Z,a), SB1));
}

/*
 * SIMD GF(2^8) multiply.
 * For each lane: p = XOR of (mask_i & xtime^i(a)) for i in 0..7,
 * where mask_i = 0xFF if bit i of b = 1, else 0x00.
 *
 * bit_mask(v, shift): isolate bit 'shift' of each byte as 0x00 or 0xFF.
 *   Step 1: shift right so the target bit is in position 0.
 *   Step 2: AND with 0x01 to isolate.
 *   Step 3: 0 - (0 or 1) = 0x00 or 0xFF.
 *
 * Note: _mm_srli_epi16 shifts 16-bit words. For byte-level right shift,
 * we mask off the bleed from the upper byte of each 16-bit word.
 */
#define MASK(v, shift) \
    _mm_sub_epi8(Z, _mm_and_si128(_mm_srli_epi16((v),(shift)), _mm_set1_epi8(1)))

static __attribute__((always_inline)) inline __m128i gfmulv(__m128i a, __m128i b) {
    __m128i m0=MASK(b,0), m1=MASK(b,1), m2=MASK(b,2), m3=MASK(b,3);
    __m128i m4=MASK(b,4), m5=MASK(b,5), m6=MASK(b,6), m7=MASK(b,7);
    __m128i a1=xtv(a), a2=xtv(a1), a3=xtv(a2), a4=xtv(a3);
    __m128i a5=xtv(a4), a6=xtv(a5), a7=xtv(a6);
    return _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(_mm_and_si128(m0,a ),_mm_and_si128(m1,a1)),
                         _mm_xor_si128(_mm_and_si128(m2,a2),_mm_and_si128(m3,a3))),
           _mm_xor_si128(_mm_xor_si128(_mm_and_si128(m4,a4),_mm_and_si128(m5,a5)),
                         _mm_xor_si128(_mm_and_si128(m6,a6),_mm_and_si128(m7,a7))));
}

/*
 * SIMD GF squaring — linear map over GF(2), all 16 bytes at once.
 * Identical logic to scalar gf_sq but on __m128i lanes.
 * lo bits: scatter even input bits to output positions 0,2,4,6.
 * hi bits (a4-a7): reduce via masks 0x1B,0x6C,0xAB,0x9A.
 */
static __attribute__((always_inline)) inline __m128i gfsqv(__m128i x) {
    /* lo: bits 0,1,2,3 → positions 0,2,4,6 */
    __m128i b0=_mm_and_si128(x,_mm_set1_epi8(0x01));           /* bit 0 → pos 0 */
    __m128i b1=_mm_slli_epi16(_mm_and_si128(x,_mm_set1_epi8(0x02)),1);  /* bit1→pos2 */
    __m128i b2=_mm_slli_epi16(_mm_and_si128(x,_mm_set1_epi8(0x04)),2);  /* bit2→pos4 */
    __m128i b3=_mm_slli_epi16(_mm_and_si128(x,_mm_set1_epi8(0x08)),3);  /* bit3→pos6 */
    __m128i lo=_mm_or_si128(_mm_or_si128(b0,b1),_mm_or_si128(b2,b3));

    /* hi: bits 4-7 with reduction constants */
    __m128i hi=_mm_xor_si128(
        _mm_xor_si128(_mm_and_si128(MASK(x,4),_mm_set1_epi8(0x1B)),
                      _mm_and_si128(MASK(x,5),_mm_set1_epi8(0x6C))),
        _mm_xor_si128(_mm_and_si128(MASK(x,6),_mm_set1_epi8((int8_t)0xAB)),
                      _mm_and_si128(MASK(x,7),_mm_set1_epi8((int8_t)0x9A))));
    return _mm_xor_si128(lo, hi);
}

/* SIMD GF inverse: Fermat x^254, optimal addition chain */
static __attribute__((always_inline)) inline __m128i gfinvv(__m128i x) {
    __m128i x2  = gfsqv(x);
    __m128i x3  = gfmulv(x2,  x);
    __m128i x6  = gfsqv(x3);
    __m128i x12 = gfsqv(x6);
    __m128i x15 = gfmulv(x12, x3);
    __m128i x30 = gfsqv(x15);
    __m128i x60 = gfsqv(x30);
    __m128i x120= gfsqv(x60);
    __m128i x240= gfsqv(x120);
    __m128i x252= gfmulv(x240, x12);
    return         gfmulv(x252, x2);
}

/* SIMD SubBytes: affine(gf_inv(x)) XOR 0x63, all 16 bytes */
static __attribute__((always_inline)) inline __m128i sbv(__m128i x) {
    __m128i s = gfinvv(x);
    __m128i r = s;
    r = _mm_xor_si128(r, _mm_or_si128(_mm_slli_epi16(s,1), _mm_srli_epi16(_mm_and_si128(s,_mm_set1_epi8((int8_t)0xFE)),7)));
    r = _mm_xor_si128(r, _mm_or_si128(_mm_slli_epi16(_mm_and_si128(s,_mm_set1_epi8(0x3F)),2), _mm_srli_epi16(_mm_and_si128(s,_mm_set1_epi8((int8_t)0xC0)),6)));
    r = _mm_xor_si128(r, _mm_or_si128(_mm_slli_epi16(_mm_and_si128(s,_mm_set1_epi8(0x1F)),3), _mm_srli_epi16(_mm_and_si128(s,_mm_set1_epi8((int8_t)0xE0)),5)));
    r = _mm_xor_si128(r, _mm_or_si128(_mm_slli_epi16(_mm_and_si128(s,_mm_set1_epi8(0x0F)),4), _mm_srli_epi16(_mm_and_si128(s,_mm_set1_epi8((int8_t)0xF0)),4)));
    return _mm_xor_si128(r, _mm_set1_epi8(0x63));
}

/* ShiftRows: pshufb */
static __attribute__((always_inline)) inline __m128i sr(__m128i s) {
    return _mm_shuffle_epi8(s,_mm_setr_epi8(0,5,10,15,4,9,14,3,8,13,2,7,12,1,6,11));
}

/* MixColumns: all 4 columns in SIMD */
static __attribute__((always_inline)) inline __m128i mc(__m128i s) {
    __m128i s1=_mm_shuffle_epi8(s,_mm_setr_epi8(1,2,3,0,5,6,7,4,9,10,11,8,13,14,15,12));
    __m128i s2=_mm_shuffle_epi8(s,_mm_setr_epi8(2,3,0,1,6,7,4,5,10,11,8,9,14,15,12,13));
    __m128i s3=_mm_shuffle_epi8(s,_mm_setr_epi8(3,0,1,2,7,4,5,6,11,8,9,10,15,12,13,14));
    __m128i T=_mm_xor_si128(_mm_xor_si128(s,s1),_mm_xor_si128(s2,s3));
    return _mm_xor_si128(_mm_xor_si128(s,T),xtv(_mm_xor_si128(s,s1)));
}

/* ================================================================ */
void AES_encrypt_custom(const unsigned char *pt, unsigned char *ct,
                        const AES_KEY_Custom *key)
{
    /* State lives in XMM register for the entire function — never hits memory */
    __m128i st = _mm_xor_si128(_mm_loadu_si128((const __m128i*)pt),
                                _mm_loadu_si128((const __m128i*)&key->rd_key[0]));

    /* Full round: SB→SR→MC→ARK */
#define R(off)  st=sbv(st); st=sr(st); st=mc(st); \
                st=_mm_xor_si128(st,_mm_loadu_si128((const __m128i*)&key->rd_key[off]));
    /* Final round: SB→SR→ARK */
#define F(off)  st=sbv(st); st=sr(st); \
                st=_mm_xor_si128(st,_mm_loadu_si128((const __m128i*)&key->rd_key[off]));

    R(4) R(8) R(12) R(16) R(20) R(24) R(28) R(32) R(36)
    F(40)

#undef R
#undef F

    _mm_storeu_si128((__m128i*)ct, st);
}

void AES_code(unsigned char pt[16], unsigned char ct[16], AES_KEY *k) {
    AES_encrypt_custom(pt, ct, (AES_KEY_Custom *)k);
}
