//
// Created by 69029 on 6/23/2021.
//
#include "utils.hpp"
#include "config_pc.hpp"
#include <math.h>
#include <omp.h>

extern int MAX_CHUNCK;
extern double proving_time;
extern unsigned long int mul_counter;
extern vector<F> x_transcript,y_transcript;
extern F current_randomness;
extern int threads;
vector<F> w;

void pad_vector(vector<F> &v){
    size_t size = v.size();
    F zero = F(0);
    if(1ULL<<((int)log2(size)) == v.size())return;
    v.resize(1ULL<<((int)log2(size) + 1),zero);
}

void init_matrix(F **&M, int rows, int cols){
    M = new F*[rows]; 
    for(int i  = 0; i < rows; i++){
        M[i] = new F[cols];
        for(int j = 0; j < cols;j ++){
            M[i][j] = F(0);
        }
    }
}

void free_matrix(F **M,int rows){
    for(int i = 0; i < rows; i++){
        //delete [] (M[i]);
        free(M[i]);
        //M[i] = NULL;
    }
    //delete[] M;
    free(M);
    M = nullptr;
    //free(M);
    //M = NULL;
}


F *init_vector( int rows){
    F *M = (F*)malloc(rows*sizeof(F));
    for(int i  = 0; i < rows; i++){
        M[i] = F(0);
    }
    return M;
}
void free_vector(F *M){
    free(M);
    M = NULL;
}

vector<F> evaluate_vector_stream_batch(stream_descriptor fp,vector<vector<F>> r, size_t size){
    int _MAX_CHUNCK = MAX_CHUNCK;
    if(_MAX_CHUNCK > size){
        _MAX_CHUNCK = size;
    }

    printf("%d,%d\n",r[0].size(),size);

    int depth = (int)log2(size) - (int)log2(_MAX_CHUNCK);
    vector<vector<F>> x1(r.size()),x2(r.size());
    
    for(int i = 0; i < (int)log2(_MAX_CHUNCK); i++){
        for(int j = 0; j < x1.size(); j++){
            x1[j].push_back(r[j][i]);
        }
    }
    
    for(int i = (int)log2(_MAX_CHUNCK); i < r[0].size(); i++){
        for(int j = 0; j < x2.size(); j++){
            x2[j].push_back(r[j][i]);
        }
    } 

    vector<vector<F>> temp_sum(x1.size());
    for(int i = 0; i < x1.size(); i++){
        temp_sum[i].resize(depth,F(0));
    }
    if(x2[0].size() != depth){
        printf("Different depth\n");
        exit(-1);
    }
    vector<F> v1(_MAX_CHUNCK);
    vector<F> final_eval(x1.size());
    for(int i = 0; i < size/_MAX_CHUNCK; i++){
        read_stream(fp,v1,_MAX_CHUNCK);
    
        for(int k = 0; k < x1.size(); k++){
            F eval1 = evaluate_vector(v1,x1[k]);
            for(int j = 0; j < temp_sum[k].size(); j++){
                if(temp_sum[k][j] == F(0)){
                    temp_sum[k][j] = eval1;
                    
                    break;
                }else{
                    eval1 = temp_sum[k][j]*(F(1) - x2[k][j]) + eval1*x2[k][j];
                    temp_sum[k][j] = F(0);
                }
            }
            final_eval[k] = eval1;
        }
    }

    return final_eval;    
}
F evaluate_vector_stream(stream_descriptor fp, vector<F> r, size_t size){
    int _MAX_CHUNCK = MAX_CHUNCK;
    if(_MAX_CHUNCK > size){
        _MAX_CHUNCK = size;
    }
    int depth = (int)log2(size) - (int)log2(_MAX_CHUNCK);
    vector<F> x1,x2;
    for(int i = 0; i < (int)log2(_MAX_CHUNCK); i++){
        x1.push_back(r[i]);
    }
    for(int i = (int)log2(_MAX_CHUNCK); i < r.size(); i++){
        x2.push_back(r[i]);
    } 

    vector<F> temp_sum(depth,F(0));
    vector<F> v1(_MAX_CHUNCK);
    F final_eval;
    for(int i = 0; i < size/_MAX_CHUNCK; i++){
        read_stream(fp,v1,_MAX_CHUNCK);
        F eval1 = evaluate_vector(v1,x1);
        for(int j = 0; j < temp_sum.size(); j++){
            if(temp_sum[j] == F(0)){
                temp_sum[j] = eval1;
                break;
            }else{
                eval1 = temp_sum[j]*(F(1) - x2[j]) + eval1*x2[j];
                temp_sum[j] = F(0);
            }
        }
        final_eval = eval1;
    }

    return final_eval;    
}

void compute_convolution(vector<vector<F>> Lv, vector<F> &B){
    int conv_size = 1;
	for(int i = 0; i < Lv.size(); i++){
		conv_size = conv_size*Lv[i].size();
		//printf("%d ", Lv[i].size());
	}
    F *_B = (F *)malloc((1)*sizeof(F));
    _B[0] = F(1);
    
	//printf("\n");
    B.resize(conv_size);
    int size = 1;
    for(int i = Lv.size()-1; i >= 0; i--){
        size *= Lv[i].size();
        F *temp_B = (F *)malloc(size*sizeof(F));
        if(i == 0){
            for(int j = 0; j < conv_size/Lv[i].size(); j++){
                for(int k = 0; k < Lv[i].size(); k++){
                    B[j* Lv[i].size() + k] = _B[j]*Lv[i][k];
                }
            }
        }else{
            for(int j = 0; j < size/Lv[i].size(); j++){
                for(int k = 0; k < Lv[i].size(); k++){
                    temp_B[j* Lv[i].size() + k] = _B[j]*Lv[i][k];
                }
            }
        }
        _B = temp_B;
    }
}

void my_fft(vector<F> &arr, vector<F> &w, vector<u32> &rev, F ilen,  bool flag){
    u32 len = arr.size();
    assert(w.size() == rev.size());
    
    if(!flag){
        //if (flag) F::inv(w[1], w[1]);
        for (u32 i = 0; i < len; ++i)
            if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
  
        F u,v;
        for (u32 i = 2; i <= len; i <<= 1){
            for (u32 j = 0; j < len; j += i)
                for (u32 k = 0; k < (i >> 1); ++k) {
                    u = arr[j + k];
                    v = arr[j + k + (i >> 1)] * w[len / i * k];
                    arr[j + k] = u + v;
                    arr[j + k + (i >> 1)] = u - v;
                }
        }

    }else{

    
        F u,v;
        for (u32 i = 0; i < len; ++i)
            if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
      
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                    u = arr[j + k];
                    v = arr[j + k + (i >> 1)] * w[len / i * k];
                    arr[j + k] = u + v;
                    arr[j + k + (i >> 1)] = u - v;
                
            }
    
        if(flag){
            for (u32 i = 0; i < len; ++i){
                arr[i] = arr[i] * ilen;
            }
        }
       
    }
}


vector<F> compute_lagrange_coeff(F omega, F r, int degree){
	vector<F> pows;
    
    vector<F> L1(degree);
	F A; 
    A = A.fastPow(r,degree);
    A = A-F(1);
    
    pows.push_back(F(1));
	for(int i = 1; i < degree; i++){
		F num = pows[i-1]*omega;
		if(num == F(1)){
			break;
		}
		pows.push_back(num);
	}
	for(int i = 0; i < pows.size(); i++){
		F temp = F(degree)*(r-pows[i]);
		temp = temp.inv();
		L1[i] = temp*A*pows[i];
	}	
	return L1;
}
void precompute_beta(vector<F> r,vector<F> &B){
    B.resize(1<<r.size());
    F *_B = (F *)malloc((1<<r.size())*sizeof(F));
    B[0] = F(1);
    _B[0] = F(1);
    for(int i = 0; i < r.size(); i++){
        
        F *temp_B = (F *)malloc((1<<i)*sizeof(F));
        
        //vector<F> temp_B(1<<i);
        //#pragma omp parallel for
        for(int j = 0; j < (1<<i); j++){
            temp_B[j] = (_B[j]);
        }
      
        //if((1ULL<<i) > 1024){
            //#pragma omp parallel
            //{
             //   int t = 1;//omp_get_thread_num();
           ///     for(int j = t*(1<<i)/threads; j < (t+1)*(1<<i)/threads; j++){
             ///       int num = j<<1;
             //       F temp = r[r.size() - 1 -i]*temp_B[j];
              //      _B[num] = temp_B[j] - temp;
            //        _B[num+1] = temp;
          //      }
            //}
        //}else{
            for(int j = 0; j < (1<<i); j++){
                int num = j<<1;
                F temp = r[r.size() - 1 -i]*temp_B[j];
                _B[num] = temp_B[j] - temp;
                _B[num+1] = temp;
            }
        //}
        
        
        free(temp_B);
     
    }
    
    for(int i = 0; i < 1<<r.size(); i++){
        B[i] = _B[i];
    }
    free(_B);
    //return B;
}
void initHalfTable(vector<F> &beta_f, vector<F> &beta_s, const vector<F>::const_iterator &r, const F &init, u64 first_half, u64 second_half) {
    beta_f.at(0) = init;
    beta_s.at(0) = F_ONE;

    for (u32 i = 0; i < first_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_f.at(j) * r[i];
            beta_f.at(j | (1ULL << i)) = tmp;
            beta_f.at(j) = beta_f[j] - tmp;
        }
    }

    for (u32 i = 0; i < second_half; ++i) {
        for (u32 j = 0; j < (1ULL << i); ++j) {
            auto tmp = beta_s[j] * r[(i + first_half)];
            beta_s[j | (1ULL << i)] = tmp;
            beta_s[j] = beta_s[j] - tmp;
        }
    }
}

void initBetaTable(vector<F> &beta_g, u8 gLength, const vector<F>::const_iterator &r, const F &init) {
    if (gLength == -1) return;

    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;

    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (init != F_ZERO) {
        initHalfTable(beta_f, beta_s, r, init, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = beta_f.at(i & mask_fhalf) * beta_s.at(i >> first_half);
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g.at(i) = F_ZERO;

    
}

void initBetaTable(vector<F> &beta_g, int gLength, const vector<F>::const_iterator &r_0,
                   const vector<F>::const_iterator &r_1, const F &alpha, const F &beta) {
    static vector<F> beta_f, beta_s;
    int first_half = gLength >> 1, second_half = gLength - first_half;
    u32 mask_fhalf = (1ULL << first_half) - 1;
    assert(beta_g.size() >= 1ULL << gLength);
    myResize(beta_f, 1ULL << first_half);
    myResize(beta_s, 1ULL << second_half);
    if (beta != F_ZERO) {
        initHalfTable(beta_f, beta_s, r_1, beta, first_half, second_half);
        for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = beta_f[i & mask_fhalf] * beta_s[i >> first_half];
    } else for (u32 i = 0; i < (1ULL << gLength); ++i)
            beta_g[i] = F_ZERO;

    if (alpha == F_ZERO) return;
    initHalfTable(beta_f, beta_s, r_0, alpha, first_half, second_half);
    assert(beta_g.size() >= 1ULL << gLength);
    for (u32 i = 0; i < (1ULL << gLength); ++i)
        beta_g[i] = beta_g[i] + beta_f[i & mask_fhalf] * beta_s[i >> first_half];
}

/*F getRootOfUnit(int n) {
    F res = -F_ONE;
    if (!n) return F_ONE;
    while (--n) {
        bool b = F::squareRoot(res, res);
        assert(b);
    }
    return res;
}
*/
vector<F> convert2vector(vector<vector<F>> M){
    vector<F> V;
    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            V.push_back(M[i][j]);
        }
    }
    return V;
}

vector<F> tensor2vector(vector<vector<vector<vector<F>>>> M){
    vector<F> V;

    for(int i = 0; i < M.size(); i++){
        for(int j = 0; j < M[i].size(); j++){
            for(int k = 0; k < M[i][j].size(); k++){
                for(int l = 0; l < M[i][j][k].size(); l++){
                    V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return V;
}


vector<vector<vector<vector<F>>>> vector2tensor(vector<F> v,vector<vector<vector<vector<F>>>> M,int w_pad){
    int N = M[0].size();
    int w = M[0][0].size();
    vector<vector<vector<vector<F>>>> M_new(M.size());
    for(int i = 0; i < M.size(); i++){
        M_new[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_new[i][j].resize(w_pad);
            for(int k = 0; k < w_pad; k++){
                M_new[i][j][k].resize(w_pad);
                for(int l = 0; l < w_pad; l++){
                    M_new[i][j][k][l] = v[i*N*w*w + j*w*w + k*w + l];
                    //V.push_back(M[i][j][k][l]);
                }
            }
        }
    }
    return M_new;
}

vector<vector<F>> convert2matrix(vector<F> arr, int d1, int d2){
    vector<vector<F>> U(d1);
    for(int i = 0; i < d1; i++){
        U[i].resize(d2);
        for(int j = 0; j < d2; j++){
            U[i][j] = arr[i*d2+j];
        }
    }
    return U;
}


vector<vector<F>> transpose(vector<vector<F>> M){
    vector<vector<F>> M_t(M[0].size());
    for(int i = 0; i < M[0].size(); i++){
        M_t[i].resize(M.size());
        for(int j = 0; j < M.size(); j++){
            M_t[i][j] = M[j][i];
        }
    }
    return M_t;
}

vector<vector<F>> rotate(vector<vector<F>> M){
    vector<vector<F>> M_r(M.size());
    for(int i = 0; i < M.size(); i++){
        M_r[i].resize(M[i].size());
        for(int j = 0; j < M[i].size(); j++){
            M_r[i][j] = M[M.size()-1-i][M[i].size()-1-j];
        }
    }
    return M_r;
}



F getRootOfUnity(int n) {
     F rou;
      rou.img = 1033321771269002680L;
        rou.real = 2147483648L;

        assert(n <= 61);

        for(int i = 0; i < 62 - n; ++i)
            rou = rou * rou;

    return rou;
}



void fft(vector<F> &arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
    std::vector<u32> rev;
    std::vector<F> w;

    u32 len = 1ULL << logn;
    assert(arr.size() == len);

    rev.resize(len);
    w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    w[0] = F_ONE;

    // Get root of unity
    F rou = getRootOfUnity(logn);
    
    //assert(log_order <= 61);

    //for (int i = 0; i < 62 - logn; ++i)
    //    rou = rou * rou;

    w[1] = rou;
    
    
    
    
    if (flag) w[1] = w[1].inv();
    for (u32 i = 2; i < len; ++i) w[i] = w[i - 1] * w[1];
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);

    
    F u,v;
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                u = arr[j + k];
                v = arr[j + k + (i >> 1)] * w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
            }

    if (flag) {
        F ilen;
        ilen = F(len).inv();
        if(ilen*len != 1){
            printf("Error in inv\n");
            exit(-1);
        }
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
            mul_counter++;
        }
    }
}

void __fft(F *&arr,  int logn, bool flag){
     std::vector<u32> rev;
    //std::vector<F> w;
  
    u32 len = 1ULL << logn;
    //assert(arr.size() == len);
    F rou = getRootOfUnity(logn);
    
    rev.resize(len);
    //w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    
    // Get root of unity
    
    //assert(log_order <= 61);

    //for (int i = 0; i < 62 - logn; ++i)
    //    rou = rou * rou;

    
    
    
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
   
     
    F *_w = new F[len];
        _w[0] = F_ONE;
        _w[1] = rou;
        if (flag) _w[1] = _w[1].inv();
        for (u32 i = 2; i < len; ++i) _w[i] = _w[i - 1] * _w[1];
    /*
    if(w.size() != len){
        printf("Initializing %d\n",len);
        w.clear();
        w.resize(len);
        w[0] = F_ONE;
        w[1] = rou;
        if (flag) w[1] = w[1].inv();
        for (u32 i = 2; i < len; ++i) w[i] = w[i - 1] * w[1];
    }
    */
    
    F u,v;
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                u = arr[j + k];
                v = arr[j + k + (i >> 1)] * _w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
            }

    delete[] _w;
   
    
    if (flag) {
        F ilen;
        ilen = F(len).inv();
        if(ilen*len != 1){
            printf("Error in inv\n");
            exit(-1);
        }
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
            mul_counter++;
        }
    }
    
    
}

void _fft(F *arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
   
    std::vector<u32> rev;
    //std::vector<F> w;

    u32 len = 1ULL << logn;
    //assert(arr.size() == len);
    F rou = getRootOfUnity(logn);
    
    rev.resize(len);
    //w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    
    // Get root of unity
    
    //assert(log_order <= 61);

    //for (int i = 0; i < 62 - logn; ++i)
    //    rou = rou * rou;

    
    
    
   
    
    
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);
    
     if(w.size() != len){
        //printf("Initializing\n");
        w.clear();
        w.resize(len);
        w[0] = F_ONE;
        w[1] = rou;
        if (flag) w[1] = w[1].inv();
        for (u32 i = 2; i < len; ++i) w[i] = w[i - 1] * w[1];
    }
    F u,v;
    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                u = arr[j + k];
                v = arr[j + k + (i >> 1)] * w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
            }

    
    if (flag) {
        F ilen;
        ilen = F(len).inv();
        if(ilen*len != 1){
            printf("Error in inv\n");
            exit(-1);
        }
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
            mul_counter++;
        }
    }
}



void phiPowInit(vector<F> &phi_mul, int n, bool isIFFT) {
    u32 N = 1ULL << n;
    F rou = getRootOfUnity(n);

    /*
    rou.img = 1033321771269002680L;
    rou.real = 2147483648L;
    for (int i = 0; i < 62 - n; ++i)
        rou = rou * rou;
    */
    
    F phi = rou;
    if (isIFFT) phi = phi.inv();
    phi_mul[0] = F_ONE;
    for (u32 i = 1; i < N; ++i) phi_mul[i] = phi_mul[i - 1] * phi;
}

void phiGInit(vector<F> &phi_g, const vector<F>::const_iterator &rx, const F &scale, int n, bool isIFFT) {
    vector<F> phi_mul(1 << n);
    phiPowInit(phi_mul, n, isIFFT);

    if (isIFFT) {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n - 1; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = phi_g[1] = scale;
        for (int i = 1; i <= n; ++i)
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }


        
    } else {
//        cerr << "==" << endl;
//        cerr << "gLength: " << n << endl;
//        for (int i = 0; i < n; ++i) {
//            cerr << rx[i];
//            cerr << endl;
//        }
        phi_g[0] = scale;
        /*
        
        for(int i = 0; i < n; i++){
            for(int j = 1ULL << (i+1)-1; j >= 0; j--){
                phi_g[j] = phi_g[j%(1ULL << i)]*(F(1)-rx[i] + rx[i]*phi_mul[j]);
            }
        }
        */

        for (int i = 1; i < n; ++i){
            for (u32 b = 0; b < (1ULL << (i - 1)); ++b) {
                u32 l = b, r = b ^ (1ULL << (i - 1));
                int m = n - i;
                
                F tmp1 = F_ONE - rx[m], tmp2 = rx[m] * phi_mul[b << m];
                //printf("%d,%d\n",r,l );
                phi_g[r] = phi_g[l] * (tmp1 - tmp2);
                phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            }

        }
        for (u32 b = 0; b < (1ULL << (n - 1)); ++b) {
            u32 l = b;

            F tmp1 = F_ONE - rx[0], tmp2 = rx[0] * phi_mul[b];
            phi_g[l] = phi_g[l] * (tmp1 + tmp2);
            
        }
        
    }
}


vector<F> prepare_matrix(vector<vector<F>> M, vector<F> r){
    vector<F> V;
    int n = M.size();
    int offset = M[0].size()/2;
    //printf(">> %d,%d,%d\n",n, M[0].size(),r.size() );
    for(int k = 0; k < r.size(); k++){
        for(int i = 0; i < n; i++){
            for(int j = 0; j < offset; j++){
                M[i][j] = M[i][2*j] + r[k]*(M[i][2*j+1]-M[i][2*j]);
            }
        }
        offset = offset/2;
    }
    for(int i = 0; i < n; i++){
        V.push_back(M[i][0]);
    }
    return V;
}

F evaluate_matrix(vector<vector<F>> M, vector<F> r1, vector<F> r2){
    vector<F> v = prepare_matrix(transpose(M),r1);
    for(int i = 0; i < r2.size(); i++){
        int L = 1 << (r2.size() - 1 - i);

        for(int j = 0; j < L; j++){
            v[j] = (F(1)-r2[i])*v[2*j] + r2[i]*v[2*j+1];
        }
    }
    return v[0];
}

F evaluate_vector(vector<F> v,vector<F> r){
    vector<F> _r;
    for(int i = 0; i < (int)log2(v.size()); i++){
        _r.push_back(r[i]);
    }
    r = _r;
    for(int i = 0; i < r.size(); i++){
        int L = 1 << (r.size() - 1 - i);
        for(int j = 0; j < L; j++){
            v[j] = (F(1)-r[i])*v[2*j] + r[i]*v[2*j+1];
        }
    }
    return v[0];    
}




vector<vector<F>> generate_tables(){
    int N = 4;
    int no_tables = 5;
    vector<vector<F>> tables(no_tables);
    vector<int> max_num;
    int exponent = 0,last_exponent = 1;
    float num = 0;
    
    for(int i = 0; i < tables.size(); i++){
        for(int j = 0; j < 1<<N; j++){
            exponent = exponent + last_exponent; 
            F num;
            num = random();//.setByCSPRNG();
            tables[i].push_back(num);
            //tables[i].push_back(quantize(exp(-dequantize(exponent,1))));
        }
        last_exponent = exponent;
        exponent = 0;
    }
    
    //printf("%f,%f\n",dequantize(prod,level),exp(-0.1) );
    return tables;
}


vector<F> get_predicates(int size){
    vector<F> poly;
    for(int i = 0; i < 1<<size; i++){
        poly.push_back(F(rand()%2));
    }
    return poly;
}

vector<vector<F>> get_poly(int size){
    vector<vector<F>> poly(1<<size);

    for(int i = 0; i < 1<<size; i++){
        poly[i].resize(1);
        poly[i][0] = F(rand()%1024);
    }
    return poly;
}
void get_int64(vector<unsigned long long int> &arr, __hhash_digest hash){
    unsigned long long int* res_array = reinterpret_cast<unsigned long long int*>(&hash.h0);
    for (int i = 0; i < 2; ++i) {
        arr[i] = res_array[i];
    }
    res_array = reinterpret_cast<unsigned long long int*>(&hash.h1);
    for(int i = 2; i < 4; i++){
        arr[i] = res_array[i-2];        
    }
}

void get_field_vector(vector<F> &h_f, vector<__hhash_digest> &h){
    F pow1 = F(1);
    F pow2 = F(1ULL<<32)*F(1ULL<<32);
    F pow3 = pow2*pow2;
    F pow4 = pow3*pow3;
    vector<unsigned long long int> arr(4);
    for(int i = 0; i < h_f.size(); i++){
        get_int64(arr,h[i]);
        h_f[i] = F(arr[0]) + pow2*arr[1] + pow3*arr[2]+pow4*arr[3];
    }
    
}

vector<F> generate_randomness(int size){
    vector<F> x;
    F c;
    for(int i = 0; i < size; i++){
        if(i % 100 == 0){
            c = random();
        }
        x.push_back(c + F(rand()));
    }
    return x;
}
void compute_binary(vector<F> r, vector<F> &B){
    B.resize(1<<r.size());
    int num;
    for(int i = 0; i < 1<<r.size(); i++){
        num = i;
        B[i] = F(1);
        for(int j = 0; j < r.size(); j++){
            if(num & 1 == 1){
                B[i] = B[i]*r[j];
            }
            //else{
            //    B[i] = B[i]*(F(1)-r[j]);
            //}
            num = num >> 1;
        }

    }
}