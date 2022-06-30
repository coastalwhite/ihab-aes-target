/*
 * Copyright (C) 2016 https://www.brobwind.com
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define AES_MAXNR        10
#define ROTL8(x,shift) ((uint8_t) ((x) << (shift)) | ((x) >> (8 - (shift))))

#undef ROTATE
#if defined(_MSC_VER) || defined(__ICC)
# define ROTATE(a,n)    _lrotl(a,n)
#elif defined(__GNUC__) && __GNUC__>=2
# if defined(__i386) || defined(__i386__) || defined(__x86_64) || defined(__x86_64__)
#   define ROTATE(a,n)    ({ register unsigned int ret;    \
                asm (            \
                "roll %1,%0"        \
                : "=r"(ret)        \
                : "I"(n), "0"(a)    \
                : "cc");        \
               ret;                \
            })
# elif defined(__arm__)
// ftp://ftp.dca.fee.unicamp.br/pub/docs/ea871/ARM/ARMGCCInlineAssemblerCookbook.pdf
#   define ROTATE(a,n)   ({ register unsigned int ret;    \
                asm (            \
                "ror %0,%0,%1"        \
                : "=r"(ret)        \
                : "I"(32 - n), "0"(a)    \
                : "cc");        \
               ret;                \
            })
# endif
#endif

typedef struct {
    uint32_t rd_key[4 * (AES_MAXNR + 1)];
    int32_t rounds;
    uint8_t sbox[256];
} AES_KEY;

int AES_set_encrypt_key(const uint8_t *userKey, const uint32_t bits, AES_KEY *key);
void AES_encrypt(const uint8_t *text, uint8_t *cipher, const AES_KEY *key);
void AES_encrypt_modified(const uint8_t *text, uint8_t *cipher, const AES_KEY *key);

#define RCON(x)                            (rcon(x) << 24)

#if STANDARD_AS_OPENSSL == 1
#define SWAP(x)                            __builtin_bswap32(x)
#else
#define SWAP(x)                            (x)
#endif


static uint8_t rcon(uint8_t i) {
    uint8_t c;

    for (c = 1; i != 1; i--)
        c = c << 1 ^ (c & 0x80 ? 0x1b : 0);

    return c;
}

// https://en.wikipedia.org/wiki/Rijndael_S-box
static void initialize_aes_sbox(uint8_t *sbox)
{
    /* loop invariant: p * q == 1 in the Galois field */
    uint8_t p = 1, q = 1;
    do {
        /* multiply p by x+1 */
        p = p ^ (p << 1) ^ (p & 0x80 ? 0x1B : 0);
        /* divide q by x+1 */
        q ^= q << 1;
        q ^= q << 2;
        q ^= q << 4;
        q ^= q & 0x80 ? 0x09 : 0;
        /* compute the affine transformation */
        sbox[p] = 0x63 ^ q ^ ROTL8(q, 1) ^ ROTL8(q, 2) ^ ROTL8(q, 3) ^ ROTL8(q, 4);
    } while (p != 1);
    /* 0 is a special case since it has no inverse */
    sbox[0] = 0x63;
}

static void initialize_aes_inv_sbox(uint8_t *inv_sbox)
{
    uint8_t sbox[256];
    int32_t i;

    initialize_aes_sbox(sbox);

    for (i = 0; i < 256; i++) inv_sbox[sbox[i]] = i;
}

int AES_set_encrypt_key(const uint8_t *userKey, const uint32_t bits, AES_KEY *key)
{
    uint32_t i, v1, v2, v3, v4, v5;

    if (bits != 128) return -1;

    key->rounds = 10;
    initialize_aes_sbox(key->sbox);

    v1 = key->rd_key[0] = SWAP(*(uint32_t *)(userKey +  0));
    v2 = key->rd_key[1] = SWAP(*(uint32_t *)(userKey +  4));
    v3 = key->rd_key[2] = SWAP(*(uint32_t *)(userKey +  8));
    v4 = key->rd_key[3] = SWAP(*(uint32_t *)(userKey + 12));

    uint8_t *sbox = key->sbox;

    for (i = 1; i <= (uint32_t)key->rounds; i++) {
        v5 = sbox[(v4 >> 24) & 0xff] <<  0 |
                sbox[(v4 >> 16) & 0xff] << 24 |
                sbox[(v4 >>  8) & 0xff] << 16 |
                sbox[(v4 >>  0) & 0xff] <<  8;
        key->rd_key[4 * i + 0] = v1 = RCON(i) ^ v5 ^ v1;
        key->rd_key[4 * i + 1] = v2 = v1 ^ v2;
        key->rd_key[4 * i + 2] = v3 = v2 ^ v3;
        key->rd_key[4 * i + 3] = v4 = v3 ^ v4;
    }

    return 0;
}

static uint32_t AES_encrypt_one_row_opt(uint32_t v1)
{
    uint32_t v2, v3, v4, v5, v6;

    v2 = ROTATE(v1, 16);
    v3 = ROTATE(v1, 24);
    v4 = ((v1 & 0xFF7F7F7F) * 2) ^ (((v1 >> 7) & 0x01010101) * 0x1B);
    v5 = ((v1 & 0x7F000000) * 2) ^ (((v1 >> 7) & 0x01010101) * 0x1B);
    v6 = ((v1 & 0xFFFF7F7F) * 2) ^ (((v1 >> 7) & 0x00010101) * 0x1B);

    return v2 ^ v3 ^ v4 ^ ((v5 ^ v1) >> 24 | (v6 ^ v1) << 8);
}

void AES_encrypt_modified(const uint8_t *text, uint8_t *cipher, const AES_KEY *key)
{
	// REFERENCE: {0x5c, 0x9, 0x62, 0x38, 0x4a, 0xdc, 0xbd, 0xc4, 0xdc, 0x9e, 0x7b, 0xec, 0x27, 0xac, 0x20, 0x51}
    int32_t v20;
    uint32_t v1, v2, v3, v4, v11, v12, v13, v14;

    v11 = SWAP(*(uint32_t *)(text +  0));
    v12 = SWAP(*(uint32_t *)(text +  4));
    v13 = SWAP(*(uint32_t *)(text +  8));
    v14 = SWAP(*(uint32_t *)(text + 12));

    v20 = 0;
	v1 = key->rd_key[4 * v20 + 0] ^ v11;
	v2 = key->rd_key[4 * v20 + 1] ^ v12;
	v3 = key->rd_key[4 * v20 + 2] ^ v13;
	v4 = key->rd_key[4 * v20 + 3] ^ v14;

    // v1 v2, v3, v4
    *(uint32_t *)(cipher +  0) = SWAP(v1);
    *(uint32_t *)(cipher +  4) = SWAP(v2);
    *(uint32_t *)(cipher +  8) = SWAP(v3);
    *(uint32_t *)(cipher + 12) = SWAP(v4);
}

int main() {
	uint8_t userKey[] = {
        0x2b, 0x7e, 0x15, 0x16, 0x28, 0xae, 0xd2, 0xa6,
        0xab, 0xf7, 0x15, 0x88, 0x09, 0xcf, 0x4f, 0x3c
    };
    uint8_t text[] = {
        'w', 'w', 'w', '.', 'b', 'r', 'o', 'b', 'w', 'i', 'n', 'd', '.', 'c', 'o', 'm'
    };
    uint8_t cipher[16];
    AES_KEY aes_key;

    memset(&aes_key, 0x00, sizeof(aes_key));

    AES_set_encrypt_key(userKey, 128, &aes_key);
    AES_encrypt_modified(text, cipher, &aes_key);
    
    printf("text: ");
    for (int i = 0; i < 16; i++) {
        printf("0x%x, ", text[i]);
    }
    printf("\n");

    printf("key: ");
    for (int i = 0; i < 16; i++) {
        printf("0x%x, ", userKey[i]);
    }
    printf("\n");

    printf("cipher: ");
    for (int i = 0; i < 16; i++) {
        printf("0x%x, ", cipher[i]);
    }
    printf("\n");

    printf("cipher XOR plain: ");
    for (int i = 0; i < 16; i++) {
        printf("0x%x, ", cipher[i] ^ text[i]);
    }
    printf("\n");
}