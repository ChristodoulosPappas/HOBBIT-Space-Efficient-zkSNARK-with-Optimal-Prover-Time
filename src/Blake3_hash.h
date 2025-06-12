#include "../Blake/blake3.h"

struct _hash{
    uint8_t arr[32];
};

typedef struct _hash;

void blake3_hash(uint8_t *src, uint8_t *dst);