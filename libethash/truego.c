//
// Created by xww on 2018/11/9.
//
#include <assert.h>
#include <inttypes.h>
#include <stddef.h>
//#include <opencl-c.h>
#include "ethash.h"
#include "fnv.h"
#include "endian.h"
#include "internal.h"
#include "data_sizes.h"
#include "sha3.h"

const int DATALENGTH = 2048;
const int PMTSIZE = 4;
const int TBLSIZE = 16;
const int HEADSIZE = 32;
const int DGSTSIZE = 32;
const int UPDATABLOCKLENGTH = 12000;
const int STARTUPDATENUM = 10240;


int genLookupTable(uint64_t plookup[], uint32_t ptable[]) {
    uint32_t lktWz = (DATALENGTH / 64);
    uint32_t lktSz = (DATALENGTH) * lktWz;

//idx := 0
    for (int k = 0; k < TBLSIZE; k++) {

        uint32_t plkt = (k) * lktSz;

        for (int x = 0; x < DATALENGTH; x++) {

            for (int y = 0; y < PMTSIZE; y++) {
                uint32_t val = ptable[k * DATALENGTH * PMTSIZE + x * PMTSIZE + y];
                if (val == 0xFFF) {
                    continue;
                }
                uint32_t vI = val / 64;
                uint32_t vR = val % 64;
                plookup[plkt + vI] |= 1 << vR;
            }
            plkt += lktWz;
        }
    }
    return 0;
}

int xor64(uint64_t val) {
    int r = 0;
    for (int k = 0; k < 64; k++) {
        r ^= val & 0x1;
        val = val >> 1;
    }
    return r;
}

uint8_t muliple(uint64_t input[], uint64_t prow[]) {
    int r = 0;
    for (int k = 0; k < 32; k++) {
        if (input[k] != 0 && prow[k] != 0) {
            r ^= xor64(input[k] & prow[k]);
        }
    }
    return r;
}

int MatMuliple(uint64_t input[], uint64_t output[], uint64_t pmat[]) {
    uint64_t *prow;
    memcpy(prow, &pmat, sizeof(pmat));
    uint8_t point = 0;

    for (int k = 0; k < 2048; k++) {
        int kI = k / 64;
        int kR = k % 64;
        uint8_t temp;
        temp = muliple(input, prow);
        output[kI] |= temp << kR;
        point += 32;
    }

    return 0;
}

int shift2048(uint64_t in[], int sf) {
    int sfI = sf / 64;
    int sfR = sf % 64;
    uint64_t mask = (1 << sfR) - 1;
    int bits = 64 - sfR;
    uint64_t res;
    if (sfI == 1) {
        uint64_t val = in[0];
        for (int k = 0; k < 31; k++) {
            in[k] = in[k + 1];
        }
        in[31] = val;
    }
    res = (in[0] & mask) << (bits);
    for (int k = 0; k < 31; k++) {
        uint64_t val = (in[k + 1] & mask) << (bits);
        in[k] = (in[k] >> (sfR)) + val;
    }
    in[31] = (in[31] >> (sfR)) + res;
    return 0;
}


int scramble(uint64_t permute_in[], uint64_t plookup[]) {
    uint64_t *ptbl;
    uint64_t permute_out[32];
    for (int k = 0; k < 64; k++) {

        int sf = (permute_in[0] & 0x7f);
        int bs = (permute_in[31] >> 60);

        memcpy(ptbl, &plookup, bs * 2048 * 32);

        MatMuliple(permute_in, permute_out, ptbl);
        shift2048(permute_out, sf);

        for (int k = 0; k < 32; k++) {
            permute_in[k] = permute_out[k];
            permute_out[k] = 0;
        }
    }
    return 0;
}


int byteReverse(uint8_t sha512_out[]) {
    for (int k = 0; k < 32; k++) {
        uint8_t temp = sha512_out[k];
        sha512_out[k] = sha512_out[63 - k];
        sha512_out[63 - k] = temp;
    }
    return 0;
}

uint8_t *fchainmining(uint64_t plookup[], uint8_t header[], uint64_t nonce) {
    uint8_t seed[64];
    uint8_t output[32];

    uint32_t val0 = (nonce & 0xFFFFFFFF);
    uint32_t val1 = (nonce >> 32);

    //4
    for (int k = 3; k >= 0; k--) {
        seed[k] = (val0) & 0xFF;
        val0 >>= 8;
    }
    //4
    for (int k = 7; k >= 4; k--) {
        seed[k] = (val1) & 0xFF;
        val1 >>= 8;
    }
    //32
    uint8_t dgst[32];
    //8-40
    for (int k = 0; k < HEADSIZE; k++) {
        seed[k + 8] = header[k];
    }

    //sha512 =makeHasher(sha3.New512())
    uint8_t sha512_out[64];

    //sha512(sha512_out, seed)
  //  SHA3_512(sha512_out, seed, 40);
    byteReverse(sha512_out);
    uint64_t permute_in[32];

    for (int k = 0; k < 8; k++) {
        for (int x = 0; x < 8; x++) {
            int sft = x * 8;
            uint8_t val = sha512_out[k * 8 + x] << (sft);
            permute_in[k] += val;
        }
    }
    for (int k = 1; k < 4; k++) {
        for (int x = 0; x < 8; x++) {
            permute_in[k * 8 + x] = permute_in[x];
        }
    }

    scramble(permute_in, plookup);
    uint8_t dat_in[256];
    for (int k = 0; k < 32; k++) {
        uint64_t val = permute_in[k];
        for (int x = 0; x < 8; x++) {
            dat_in[k * 8 + x] = (val & 0xFF);
            val = val >> 8;
        }
    }

    for (int k = 0; k < 64; k++) {
        uint8_t temp = dat_in[k * 4];
        dat_in[k * 4] = dat_in[k * 4 + 3];
        dat_in[k * 4 + 3] = temp;
        temp = dat_in[k * 4 + 1];
        dat_in[k * 4 + 1] = dat_in[k * 4 + 2];
        dat_in[k * 4 + 2] = temp;
    }

    //sha256 = makeHasher(sha3.New256())

    //sha256(output, dat_in);
   //  SHA3_256(output, dat_in, 64 + 32); // Keccak-256(s + compressed_mix)
   // reverse byte
    for (int k = 0; k < DGSTSIZE; k++) {
        dgst[k] = output[k];
    }

    return dgst;
}

/**int main() {
    printf("This is 1\n");
    ethash_return_value_t *ret;
    uint64_t const nonce="0x0000000000000000000000000000000000000000000000000000000000000000";
   // ethash_h256_t const header_hash="00000009e86c22b7585eb187c0fe280";
    uint8_t header_hash[32] ="0x00000009e86c22b7585eb187c0fe280e9a4d4d2019574b56d8c40e8d7ab0ad6a";
    uint64_t full_size = 1;
    uint64_t *p0value = (uint64_t *) malloc(sizeof(uint64_t) * full_size);
    // uint64_t plookup [], uint8_t header [],uint64_t nonce
    long long size = 32;
    uint8_t header[32];
    memcpy(header, &header_hash, size);
    // fchainmining( plookup []uint64, header []byte, nonce uint64) ([]byte, []byte)fchainminingReturn result  = fchainmining(p0,p1,p2);
    printf("This is 2\n");
    fchainmining(p0value, header, nonce);
    printf("This is 3\n");
    return 0;
}**/