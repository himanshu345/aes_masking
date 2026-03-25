/*
 * simpleserial-algo2.c
 *
 * Algorithm 2: Table Re-computation based IPM Masked AES-128
 * Reference: "Table Re-Computation Based Low Entropy Inner Product Masking"
 *            DATE 2023 — Ming et al.
 *
 * IPM encoding:  actual[j]  =  ST1[j]  XOR  (l2 * ST2[j])
 *
 * SimpleSerial commands:
 *   'k' (16 bytes) : set AES-128 key
 *   'p' (16 bytes) : plaintext -> Algorithm 1 (build MSBox) +
 *                    Algorithm 2 (masked AES) -> ciphertext[16]
 *
 * Trigger: HIGH at start of AES rounds, LOW after round 10 completes.
 * The mask randomness (r[16], r_in, r_out) is generated internally via
 * an xorshift32 PRNG — unique per call, unknown to the host.
 * Correctness verification: ciphertext should match standard AES(pt, key).
 */

#include "hal.h"
#include <stdint.h>
#include <string.h>
#include "simpleserial.h"

/* ── AES SBox (FIPS 197) ─────────────────────────────────────────────────── */
static const uint8_t SBOX[256] = {
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
};

/* ── AES Round Constants (RC[1..10]) ─────────────────────────────────────── */
static const uint8_t RCON[11] = {
    0x00,0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36
};

/* ── GF(2^8) arithmetic (AES field, poly 0x11B) ──────────────────────────── */
static uint8_t gf_mul(uint8_t a, uint8_t b)
{
    uint8_t p = 0;
    for (uint8_t i = 0; i < 8; i++) {
        if (b & 1) p ^= a;
        if (a & 0x80) a = ((a << 1) & 0xFF) ^ 0x1B;
        else          a = (a << 1) & 0xFF;
        b >>= 1;
    }
    return p;
}

static uint8_t gf_inv(uint8_t a)
{
    /* a^254 via square-and-multiply (Fermat's little theorem) */
    if (a == 0) return 0;
    uint8_t r = 1, base = a, e = 254;
    while (e) {
        if (e & 1) r = gf_mul(r, base);
        base = gf_mul(base, base);
        e >>= 1;
    }
    return r;
}

static uint8_t xtime(uint8_t a)
{
    return (a & 0x80) ? (((a << 1) & 0xFF) ^ 0x1B) : ((a << 1) & 0xFF);
}

/* ── Global IPM / AES state ──────────────────────────────────────────────── */
static uint8_t  l2 = 23;          /* IPM parameter (optimal set V, default 23) */
static uint8_t  L[256];            /* L[i]  = l2     * i  in GF(2^8)            */
static uint8_t  Ln[256];           /* Ln[i] = l2^-1  * i  in GF(2^8)            */
static uint8_t  AES_KEY[16];
static uint8_t  RK[176];           /* 11 round keys × 16 bytes                   */
static uint8_t  MSBox[256];        /* Masked SBox (rebuilt each call)            */

/* ── PRNG: xorshift32 ────────────────────────────────────────────────────── */
static uint32_t rng_state = 0xDEADBEEF;
static uint8_t prng_next(void)
{
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 17;
    rng_state ^= rng_state <<  5;
    return (uint8_t)(rng_state & 0xFF);
}

/* ── Build L / Ln tables from l2 ─────────────────────────────────────────── */
static void build_tables(void)
{
    uint8_t l2_inv = gf_inv(l2);
    for (uint16_t i = 0; i < 256; i++) {
        L[i]  = gf_mul(l2,     (uint8_t)i);
        Ln[i] = gf_mul(l2_inv, (uint8_t)i);
    }
}

/* ── AES-128 Key Expansion ───────────────────────────────────────────────── */
/*
 * State layout (column-major, FIPS 197):
 *   index = col*4 + row   (row 0..3, col 0..3)
 *   Words: W[j] occupies bytes RK[j*4 .. j*4+3]
 */
static void key_expansion(const uint8_t *key)
{
    memcpy(RK, key, 16);
    for (uint8_t i = 4; i < 44; i++) {
        uint8_t *wc  = &RK[i * 4];
        uint8_t *wp  = &RK[(i - 1) * 4];
        uint8_t *wm4 = &RK[(i - 4) * 4];
        if ((i & 3) == 0) {
            /* T = SubBytes(RotWord(W[i-1])) XOR Rcon[i/4] */
            wc[0] = SBOX[wp[1]] ^ wm4[0] ^ RCON[i >> 2];
            wc[1] = SBOX[wp[2]] ^ wm4[1];
            wc[2] = SBOX[wp[3]] ^ wm4[2];
            wc[3] = SBOX[wp[0]] ^ wm4[3];
        } else {
            wc[0] = wp[0] ^ wm4[0];
            wc[1] = wp[1] ^ wm4[1];
            wc[2] = wp[2] ^ wm4[2];
            wc[3] = wp[3] ^ wm4[3];
        }
    }
}

/* ── AES ShiftRows (operates on both ST1 and ST2) ────────────────────────── */
/*
 * Row r is cyclically shifted left by r positions.
 * With column-major layout (index = col*4 + row):
 *   Row 0  (indices  0, 4, 8,12): no change
 *   Row 1  (indices  1, 5, 9,13): shift left 1
 *   Row 2  (indices  2, 6,10,14): shift left 2 (= swap pairs)
 *   Row 3  (indices  3, 7,11,15): shift left 3 (= shift right 1)
 */
static void shift_rows(uint8_t *s)
{
    uint8_t tmp;
    /* Row 1 */
    tmp = s[1];  s[1]  = s[5]; s[5]  = s[9]; s[9]  = s[13]; s[13] = tmp;
    /* Row 2 */
    tmp = s[2];  s[2]  = s[10]; s[10] = tmp;
    tmp = s[6];  s[6]  = s[14]; s[14] = tmp;
    /* Row 3 */
    tmp = s[15]; s[15] = s[11]; s[11] = s[7]; s[7]  = s[3]; s[3]  = tmp;
}

/* ── AES MixColumns ──────────────────────────────────────────────────────── */
/*
 * MixColumns matrix (GF(2^8)):
 *   [2 3 1 1]
 *   [1 2 3 1]
 *   [1 1 2 3]
 *   [3 1 1 2]
 * Applied column-by-column; column c = bytes s[c*4 .. c*4+3].
 * Both ST1 and ST2 are passed through independently — the IPM encoding
 * actual[j] = ST1[j] XOR (l2 * ST2[j]) is preserved because MixColumns
 * is GF(2^8)-linear.
 */
static void mix_columns(uint8_t *s)
{
    for (uint8_t c = 0; c < 4; c++) {
        uint8_t a0 = s[c*4], a1 = s[c*4+1], a2 = s[c*4+2], a3 = s[c*4+3];
        s[c*4+0] = xtime(a0) ^ (xtime(a1) ^ a1) ^  a2              ^  a3;
        s[c*4+1] =  a0       ^  xtime(a1)        ^ (xtime(a2) ^ a2) ^  a3;
        s[c*4+2] =  a0       ^  a1               ^  xtime(a2)       ^ (xtime(a3) ^ a3);
        s[c*4+3] = (xtime(a0) ^ a0) ^ a1         ^  a2              ^  xtime(a3);
    }
}

/* ── Algorithm 1: build MSBox (offline masked SBox pre-computation) ───────── */
/*
 *  for i = 0 to 255:
 *    MSBox[i] = Ln[ SBox[ r_in XOR L[i] ] XOR r_out ]
 */
static void algo1(uint8_t r_in, uint8_t r_out)
{
    for (uint16_t i = 0; i < 256; i++) {
        uint8_t tmp = SBOX[r_in ^ L[i]];
        MSBox[i]    = Ln[tmp ^ r_out];
    }
}

/* ── Masked SubBytes (Algorithm 2 lines 6-8, applied to all 16 bytes) ──────── */
/*
 *  ST2[j] <- Ln[ST1[j] XOR r_in]  XOR ST2[j]   (line 6)
 *  ST2[j] <- MSBox[ST2[j]]                       (line 7)
 *  ST2[j] <- Ln[ST1[j] XOR r_out] XOR ST2[j]   (line 8)
 *
 * ST1 is unchanged.  After this, actual[j] = ST1[j] XOR l2*ST2[j] = SBox(x).
 */
static void sub_bytes_masked(uint8_t *st1, uint8_t *st2,
                              uint8_t r_in, uint8_t r_out)
{
    for (uint8_t j = 0; j < 16; j++) {
        st2[j] = Ln[st1[j] ^ r_in]  ^ st2[j];
        st2[j] = MSBox[st2[j]];
        st2[j] = Ln[st1[j] ^ r_out] ^ st2[j];
    }
}

/* ── SimpleSerial 'k': set AES-128 key (16 bytes) ────────────────────────── */
static uint8_t cmd_setkey(uint8_t *data, uint8_t len)
{
    (void)len;
    memcpy(AES_KEY, data, 16);
    key_expansion(AES_KEY);
    return 0x00;
}

/* ── SimpleSerial 'p': run Algorithm 1 + Algorithm 2 ────────────────────── */
/*
 * Input : pt[16]  — 16-byte plaintext
 * Output: ct[16]  — 16-byte ciphertext (standard AES(pt, key))
 *
 * Internally generates fresh random r[16], r_in, r_out via PRNG.
 * The trigger is HIGH for the entire 10-round AES computation.
 */
static uint8_t cmd_run(uint8_t *pt, uint8_t len)
{
    (void)len;

    /* ── 1. Fresh random masks ─────────────────────────────────────────── */
    uint8_t r[16], r_in, r_out;
    for (uint8_t i = 0; i < 16; i++) r[i] = prng_next();
    r_in  = prng_next();
    r_out = prng_next();

    /* ── 2. Algorithm 1: build masked SBox ────────────────────────────── */
    algo1(r_in, r_out);

    /* ── 3. Encode plaintext into two IPM shares ──────────────────────── */
    /*
     *  ST1[j] = r[j] XOR pt[j]          (first share)
     *  ST2[j] = Ln[r[j]]                 (second share = l2^-1 * r[j])
     *
     *  Invariant: actual[j] = ST1[j] XOR (l2 * ST2[j])
     *           = (r[j] XOR pt[j]) XOR (l2 * l2^-1 * r[j])
     *           = (r[j] XOR pt[j]) XOR r[j]
     *           = pt[j]  ✓
     */
    uint8_t st1[16], st2[16];
    for (uint8_t j = 0; j < 16; j++) {
        st1[j] = r[j] ^ pt[j];
        st2[j] = Ln[r[j]];
    }

    /* ── 4. Add initial round key to ST1 (Algorithm 2 line 3) ─────────── */
    for (uint8_t j = 0; j < 16; j++) st1[j] ^= RK[j];

    trigger_high();  /* START of measurement window */

    /* ── 5. Rounds 1–9 (SubBytes + ShiftRows + MixColumns + AddRoundKey) */
    for (uint8_t rnd = 1; rnd <= 9; rnd++) {
        sub_bytes_masked(st1, st2, r_in, r_out);
        shift_rows(st1);
        shift_rows(st2);
        mix_columns(st1);
        mix_columns(st2);
        for (uint8_t j = 0; j < 16; j++) st1[j] ^= RK[rnd * 16 + j];
    }

    /* ── 6. Round 10 (SubBytes + ShiftRows + AddRoundKey, no MixColumns) */
    sub_bytes_masked(st1, st2, r_in, r_out);
    shift_rows(st1);
    shift_rows(st2);
    for (uint8_t j = 0; j < 16; j++) st1[j] ^= RK[160 + j];

    trigger_low();   /* END of measurement window */

    /* ── 7. Decode shares: ct[j] = ST1[j] XOR L[ST2[j]]              */
    /*      L[ST2[j]] = l2 * ST2[j], so ct = ST1 XOR l2*ST2 = actual  */
    uint8_t ct[16];
    for (uint8_t j = 0; j < 16; j++) ct[j] = st1[j] ^ L[st2[j]];

    simpleserial_put('r', 16, ct);
    return 0x00;
}

/* ── Main ─────────────────────────────────────────────────────────────────── */
int main(void)
{
    platform_init();
    init_uart();
    trigger_setup();

    /* Default: all-zero key, l2 = 23, build tables */
    memset(AES_KEY, 0x00, 16);
    key_expansion(AES_KEY);
    build_tables();

    simpleserial_init();
    simpleserial_addcmd('k', 16, cmd_setkey);
    simpleserial_addcmd('p', 16, cmd_run);

    while (1) simpleserial_get();
}
