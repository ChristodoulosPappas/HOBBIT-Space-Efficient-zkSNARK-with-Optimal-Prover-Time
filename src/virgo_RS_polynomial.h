#ifndef __RS_polynomial
#define __RS_polynomial

#include "my_hhash.h"
#include "virgo_merkle_tree.h"
#include "virgo_prime_field.h"
#include <cassert>
#include "constants.h"

void init_scratch_pad(long long order);

extern prime_field::field_element* twiddle_factor;

//Given coefficient of polynomials, output the evaluations on the group generated by root of unity(RoT) [RoT^i for i in range(order)]
void fast_fourier_transform(const prime_field::field_element *coefficients, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *result, prime_field::field_element *twiddle_fac = twiddle_factor);


//see https://codeforces.com/blog/entry/48798 for tutorial
void inverse_fast_fourier_transform(prime_field::field_element *evaluations, int coef_len, int order, prime_field::field_element root_of_unity, prime_field::field_element *result);

#endif