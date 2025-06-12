#ifndef __vpd_prover
#define __vpd_prover
#include "virgo_prime_field.h"
#include "my_hhash.h"
__hhash_digest vpd_prover_init(prime_field::field_element *l_eval, prime_field::field_element *&l_coef, int log_input_length, int slice_size, int slice_count);
#endif