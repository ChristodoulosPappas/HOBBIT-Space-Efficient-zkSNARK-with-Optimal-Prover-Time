#include "Blake3_hash.h"



void blake3_hash(uint8_t *src, uint8_t *dst){
    blake3_hasher hasher;
    blake3_hasher_init(&hasher);
    blake3_hasher_update(&hasher, src, 64);
    blake3_hasher_finalize(&hasher, dst, 32);
}