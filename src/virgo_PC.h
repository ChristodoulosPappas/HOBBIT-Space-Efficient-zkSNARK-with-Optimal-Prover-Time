#include "config_pc.hpp"
#include "my_hhash.h"

__hhash_digest virgo_commit(vector<F> &poly);
void virgo_open(vector<F> &poly, vector<F> x, __hhash_digest C, double &vt, double &ps);