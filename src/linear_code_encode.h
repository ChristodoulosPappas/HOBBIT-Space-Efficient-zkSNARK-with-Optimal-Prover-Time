#pragma once
#include "expanders.h"

extern F *scratch[2][100];
extern unsigned long int scratch_size[100];
extern int mul_count;
extern bool __encode_initialized;

inline int encode_monolithic_alt(const F *src, F *dst, long long n,F *_scratch[2][100], int dep = 0)
{
    
    if(n <= distance_threshold)
    {
        for(long long i = 0; i < n; ++i)
            //dst[i] = src[i];
        return n;
    }
    for(long long i = 0; i < n; ++i)
    {
        //_scratch[0][dep][i] = src[i];
    }
    
    
    long long R = alpha * n;
    for(long long j = 0; j < R; ++j)
        //_scratch[1][dep][j] = F(0ULL);
    //expander mult
    for(long long i = 0; i < n; ++i)
    {
        const F &val = src[i];
        for(int d = 0; d < _C[dep].degree; ++d)
        {
            int target = _C[dep].neighbor[i][d];
            //_scratch[1][dep][target] = _scratch[1][dep][target] + _C[dep].weight[i][d] * val;
            mul_count++;
        }
    }
    long long L = encode_monolithic_alt(_scratch[1][dep], &_scratch[0][dep][n], R,_scratch, dep + 1);
    assert(D[dep].L = L);
    R = D[dep].R;
    for(long long i = 0; i < R; ++i)
    {
        //_scratch[0][dep][n + L + i] = F(0ULL);
    }
    for(long long i = 0; i < L; ++i)
    {
        //F &val = _scratch[0][dep][n + i];
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d];
            //_scratch[0][dep][n + L + target] = _scratch[0][dep][n + L + target] + val * D[dep].weight[i][d];
            mul_count++;
        }
    }
    for(long long i = 0; i < n + L + R; ++i)
    {
        //dst[i] = _scratch[0][dep][i];
    }
    return n + L + R;
}

inline int encode_monolithic(const F *src, F *dst, long long n, int dep = 0)
{
   if(!__encode_initialized)
    {
        __encode_initialized = true;
        for(int i = 0; (n >> i) > 1; ++i)
        {
            scratch[0][i] = new F[2 * n >> i];
            scratch[1][i] = new F[2 * n >> i];
        }
    }
    if(n <= distance_threshold)
    {
        for(long long i = 0; i < n; ++i)
            dst[i] = src[i];
        return n;
    }
    for(long long i = 0; i < n; ++i)
    {
        scratch[0][dep][i] = src[i];
    }
    long long R = alpha * n;
    for(long long j = 0; j < R; ++j)
        scratch[1][dep][j] = F(0ULL);
    //expander mult
    for(long long i = 0; i < n; ++i)
    {
        const F &val = src[i];
        for(int d = 0; d < _C[dep].degree; ++d)
        {
            int target = _C[dep].neighbor[i][d];
            scratch[1][dep][target] = scratch[1][dep][target] + _C[dep].weight[i][d] * val;
            mul_count++;
        }
    }
    long long L = encode_monolithic(scratch[1][dep], &scratch[0][dep][n], R, dep + 1);
    assert(D[dep].L = L);
    R = D[dep].R;
    for(long long i = 0; i < R; ++i)
    {
        scratch[0][dep][n + L + i] = F(0ULL);
    }
    for(long long i = 0; i < L; ++i)
    {
        F &val = scratch[0][dep][n + i];
        for(int d = 0; d < D[dep].degree; ++d)
        {
            long long target = D[dep].neighbor[i][d];
            scratch[0][dep][n + L + target] = scratch[0][dep][n + L + target] + val * D[dep].weight[i][d];
            mul_count++;
        }
    }
    for(long long i = 0; i < n + L + R; ++i)
    {
        dst[i] = scratch[0][dep][i];
    }
    return n + L + R;
}


inline int encode(const F *src, F *dst, long long n, int dep = 0)
{
    if(!__encode_initialized)
    {
        __encode_initialized = true;
        for(int i = 0; (n >> i) > 1; ++i)
        {
            scratch[0][i] = new F[2 * n >> i];
            scratch[1][i] = new F[2 * n >> i];
            scratch_size[i] = (2 * n >> i);
        }
    }
    if(n <= distance_threshold)
    {
        for(long long i = 0; i < n; ++i)
            dst[i] = src[i];
        return n;
    }
    
    for(long long i = 0; i < n; ++i)
    {
        scratch[0][dep][i] = src[i];
    }
    long long R = alpha * n;
    for(long long j = 0; j < R; ++j)
        scratch[1][dep][j] = F(0ULL);
    //expander mult
    F weight;


    srand(666+dep);
    for(long long i = 0; i < n; ++i)
    {
        const F &val = src[i];
        for(int d = 0; d < _C[dep].degree; ++d)
        {
            int target = rand()%(_C[dep].R);
            weight = rand();
            scratch[1][dep][target] = scratch[1][dep][target] + weight * val;
        }
    }
    long long L = encode(scratch[1][dep], &scratch[0][dep][n], R, dep + 1);
    assert(D[dep].L = L);
    R = D[dep].R;
    for(long long i = 0; i < R; ++i)
    {
        scratch[0][dep][n + L + i] = F(0ULL);
    }
    srand(2*(666+dep));
    for(long long i = 0; i < L; ++i)
    {
        F &val = scratch[0][dep][n + i];
        for(int d = 0; d < D[dep].degree; ++d)
        {
            weight = rand();
            long long target = rand()%D[dep].R;
            //long long target = D[dep].neighbor[i][d];
            scratch[0][dep][n + L + target] = scratch[0][dep][n + L + target] + val * weight;
        }
    }
   for(long long i = 0; i < n + L + R; ++i)
    {
        dst[i] = scratch[0][dep][i];
    }
    delete scratch[0][dep];
    delete scratch[1][dep];
    __encode_initialized = false;
        
    return n + L + R;
}