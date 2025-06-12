#include "config_pc.hpp"
#include "constants.h"
#include <vector>
#include "poly_commit.h"
#include <math.h>
#include "utils.hpp"
#include "Kopis.h"
#include "Virgo.h"
#include "linear_code_encode.h"
#include "sumcheck.h"
#include "mimc.h"
#include <chrono>
#include <fcntl.h>
#include "witness_stream.h"
#include "GKR.h"
#include "prover.h"
#include "Elastic_PC.hpp"
#include <omp.h>
#include "virgo_PC.h"
#include "Our_PC.hpp"
#include "Virgo.h"
#include "prove_encodings.h"
#include "GKR_standard.h"
#include <unistd.h>
#include "Seval.h"
#include <mutex>

int MAX_CHUNK;
int MAX_CHUNCK_COMM;
int PC_scheme,Commitment_hash;
int tensor_row_size = 128;
extern int _graph_nodes;
int mul_count = 0;
double proving_time = 0.0;
unsigned long int mul_counter;
vector<F> x_transcript,y_transcript;
F current_randomness;
size_t BUFFER_SPACE;
int MAX_CHUNCK;
extern layeredCircuit C;
int recursion = 0;
int threads = 1;
extern double verification_time;
extern int _proof_len;
extern bool linear_time;
int mod;
vector<unsigned int> preimage;
vector<unsigned int> SHA;
vector<int> H;
vector<F> V_in;

F a_w,b_w;

int fun = 6;
size_t input_size = 32*1024;
int depth = 127;
tr_tuple *tr;
int BUFFER_SPACE_tr;
mutex mtx,mtx2;
size_t circuit_size;
size_t lookup_size;
extern int *addresses;
extern F *values;
extern int *accesses;
extern uint8_t *types; 
extern double routine_time;
vector<F> lookup_rand;
extern vector<vector<int>> access_table;
extern vector<vector<int>> lookup_table;
bool has_lookups;
size_t gates = 0,ops = 0;
extern double prune_rate;
shockwave_data *C_x;
vector<int> layer_size;
void init_SHA(){
	for(int i = 0; i < 64; i++){
		SHA.push_back((random()%(1ULL<<32)));
	}
	for(int i = 0; i < 8; i++){
		H.push_back((random()%(1ULL<<32)));
	}
}



void compute_rs(vector<F> &betas, vector<F> &r, int logn, int l,int pos){
    int N = (1ULL<<(logn-l));
    for(int i = 0; i < N/2; i++){
        //buff[i] = r[l];
        betas[pos + i + N/2] *= r[l];
    }
   
    if(l+1 == logn){
        return;
    }
    compute_rs(betas,r,logn,l+1,pos);
    compute_rs(betas,r,logn,l+1,pos+N/2);    
}

void test(vector<F> &poly){
    vector<F> new_poly = poly;
    change_form(new_poly, (int)log2(new_poly.size()), 0,0);
    vector<F> r = generate_randomness((int)log2(poly.size()));
    F y1 = evaluate_vector(poly,r);
    F y2 = F(0);
    vector<F> betas(poly.size(),F(1));
    compute_rs(betas, r, (int)log2(new_poly.size()), 0,0);
    for(int i  = 0; i < betas.size(); i++){
        y2 += betas[i]*new_poly[i];
    }

    if(y1 != y2){
        printf("ERROR\n");
    }
}

void test_iter(int n){
    vector<F> poly = generate_randomness(1ULL<<n);
    vector<F> reduced_poly(poly.size()/4);
    F a = random();
    F b = random();
    vector<F> new_poly = poly;
    change_form(new_poly, (int)log2(poly.size()), 0,0);
    for(int i = 0; i < reduced_poly.size(); i++){
        reduced_poly[i] = (F(1)-b)*(F(1)-a)*poly[i] + (b)*(F(1)-a)*poly[i+reduced_poly.size()]+
        (F(1)-b)*a*poly[i+2*reduced_poly.size()] + a*b*poly[i+3*reduced_poly.size()];
    }
  
    vector<F> new_reduced_poly = reduced_poly;
    change_form(new_reduced_poly,(int)log2(new_reduced_poly.size()),0,0);
   
    new_poly.resize(2*new_poly.size(),F(0));
    new_reduced_poly.resize(2*new_reduced_poly.size(),F(0));
   
    fft(new_poly,(int)log2(new_poly.size()),false);
   
   
    fft(new_reduced_poly,(int)log2(new_reduced_poly.size()),false);
    
    vector<vector<F>> pairs(new_poly.size()/4);
    for(int i = 0; i < pairs.size(); i++){
            pairs[i].push_back(new_poly[i]);
            pairs[i].push_back(new_poly[i+2*new_reduced_poly.size()]);
            pairs[i].push_back(new_poly[i+new_reduced_poly.size()]);
            pairs[i].push_back(new_poly[i+3*new_reduced_poly.size()]);
        
    }
    vector<F> r(2);r[0] = a;r[1] = b;
    for(int i = 0; i < new_reduced_poly.size(); i++){
        if(new_reduced_poly[i] != fold(i,pairs[i],r,new_poly.size(),2)){
            printf("Error %d\n",i);
            exit(-1);
        }
    }

}

void tensor_test(int N,int k){
    int rows = 1<<k;
    int columns = N/rows;
    expander_init_store(columns);    
   
    vector<vector<F>> M(columns);
    vector<vector<F>> tensor(2*columns);
    for(int i = 0; i < M.size(); i++){
        M[i] = generate_randomness(rows);
    }
    
    
    for(int i = 0; i < tensor.size(); i++){
        tensor[i].resize(2*rows,F(0));
        if(i < columns){
            for(int j = 0; j < rows; j++){
                tensor[i][j] = M[i][j];
            }
        }
    }
    
    
    auto start = std::chrono::steady_clock::now();
    for(int i = 0; i < columns; i++){
        fft(tensor[i],1+(int)(log2(rows)),false);
    }
    auto end = std::chrono::steady_clock::now();
    double elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
    std::cout << "Time taken: " << elapsed_seconds << " seconds" << std::endl;

    vector<F> buff(columns);
    vector<F> buff1(2*columns);
    
    start = std::chrono::steady_clock::now();
    for(int j = 0; j < 2*rows; j++){
        for(int i = 0; i < columns; i++){
            buff[i] = tensor[i][j];
        }
        encode_monolithic(buff.data(),buff1.data(),buff.size());
        for(int i = 0; i < 2*columns; i++){
            tensor[i][j] = buff1[i];
        }
        /*
        for(int i = 0; i < columns; i++){
            buff1[i] = tensor[i][j];
        }
        fft(buff1,(int)log2(buff1.size()),false);
        for(int i = 0; i < 2*columns; i++){
            tensor[i][j] = buff1[i];
            buff1[i] = F(0);
        }
        */
    }
    end = std::chrono::steady_clock::now();
    std::cout << "Total time: " << std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count() << " seconds" << std::endl;
    elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
    std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;

    
    vector<F> poly = generate_randomness(N);
    poly.resize(2*N);

    start = std::chrono::steady_clock::now();
    fft(poly,(int)log2(2*N),false);   
    end = std::chrono::steady_clock::now();
    elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
    std::cout << "FFT time taken: " << elapsed_seconds << " seconds" << std::endl;

}

void test2(F **&arr){
    for(int i = 0; i < 1ULL<<10; i++){
        __fft(arr[i],10,false);
    }
}

void test(){
    sleep(2);

    F **arr = new F*[(1ULL<<10)];
    
    for(int i = 0; i < 1ULL<<10; i++){
        arr[i] = new F[1ULL<<10]();
        for(int j = 0; j < 1ULL<<10; j++){
            arr[i][j] = F(j);
        }
    }
    
    test2(arr);
    sleep(2);
    for(int i = 0; i < 1ULL<<10; i++){
        delete[] arr[i];
    }
    delete[] arr;
    printf("OK\n");
   
}
void test3(){
    sleep(2);
    F *arr = new F[(1ULL<<20)];
    
    for(int i = 0; i < 1ULL<<20; i++){
        arr[i] = F(i);
    }
    
    //test2(arr);
    sleep(2);
    delete[] arr;
    printf("OK\n");
   
}

void _read_tr(){
    
    while(true){
        mtx.unlock();
        mtx2.lock();

        for(int i = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 255){
                return;
            }
        }
    }
}

vector<tr_tuple> read_tr(){
    vector<tr_tuple> buff;

    int counter = 0;
    while(true){
        mtx.unlock();
        mtx2.lock();
      
        for(int i = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 255){
                return buff;
            }else{
                buff.push_back(tr[i]);
            }
        }
    }
}


size_t get_circuit_size(){
    size_t circuit_size = 0;
    while(true){
        mtx.unlock();
        mtx2.lock();
        
        for(int i = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 255){
                if(1ULL<<((int)log2(circuit_size)) != circuit_size){
                    circuit_size = 1ULL<<((int)log2(circuit_size)+1);
                    return circuit_size;
                }
                return circuit_size;
            }else if(tr[i].type == 0){
                circuit_size++;
            }
        }
    }
}

size_t check_correctness(){
    vector<tr_tuple> buff = read_tr();
    size_t delete_count = 0,add_count = 0;
    for(int i = 0; i < buff.size(); i++){
        if(buff[i].type){
            add_count++;
        }else{
            delete_count++;
        }
    }
    
    size_t gates = 0,ops = 0;
    get_circuit_info(gates, ops);
    printf(" ==== %lld,%lld ===== \n", gates,ops);
    printf(" ==== %lld,%lld ===== \n", delete_count,add_count);
    
    printf("%d,%d\n",add_count*3,delete_count*3);
    vector<int> delete_indexes;
    for(int i  = 0; i < buff.size(); i++){
        if(!buff[i].type){
            delete_indexes.push_back(buff[i].idx_o);
        }
    }
    sort(delete_indexes.begin(),delete_indexes.end());
    for(int i = 1; i < delete_indexes.size(); i++){
        if((delete_indexes[i-1] +1) != (delete_indexes[i])){
            printf("Error in deletions %d\n", i);
            exit(-1);
        }
    }
    for(int i = 0; i < buff.size(); i++){
        if(buff[i].type == 1 && buff[i].value_o != buff[i].value_l + buff[i].value_r){
            printf("Error\n");
            exit(-1);
        }else if(buff[i].type == 2 && buff[i].value_o != buff[i].value_l*buff[i].value_r){
            printf("Error mul\n");
            exit(-1);
        }
    }
    printf("Gates before padding : %lld , ",delete_count);
    if(1ULL << ((int)log2(delete_count)) != delete_count){
        delete_count = 1ULL << ((int)log2(delete_count)+1);
    }
    printf("Gates : %lld \n",delete_count);
    return delete_count;
}

void test_lookup_stream(){
    printf("Lookups : %d\n",lookup_size);
    stream_descriptor fd;fd.name = "lookup_basic"; fd.size = ops;
    reset_stream(fd);
    lookup_rand = generate_randomness(4);
    vector<F> buff(2*BUFFER_SPACE);
    F prod_r = F(1),prod_w = F(1);
    vector<F> r1,r2;
    for(int i = 0; i < 2*fd.size/buff.size(); i++){
        read_stream(fd,buff,2*BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_r *= buff[j];
            r1.push_back(buff[j]);
            prod_w *= buff[j + BUFFER_SPACE];
        }
    }
    
    F prod_i = F(1),prod_f = F(1);
    for(int j = 0; j < access_table[0].size(); j++){
        prod_i *= (F(j) +F(1)+ F(lookup_table[0][j])*lookup_rand[1]+F(3)*lookup_rand[3]);
        prod_f *= (F(j) +F(1)+ F(lookup_table[0][j])*lookup_rand[1] + lookup_rand[2]*F(access_table[0][j]) +F(3)*lookup_rand[3]);
    }
    
    for(int i = 1; i < access_table.size(); i++){
        for(int j = 0; j < access_table[i].size(); j++){
            int idx1 = j%256;
            int idx2 = j>>8;
            prod_i *= (F(idx1) + F(1)+ F(idx2)*lookup_rand[0] + F(lookup_table[i][j])*lookup_rand[1]
                +F(i+3)*lookup_rand[3]);
            prod_f *= (F(idx1) + F(1)+F(idx2)*lookup_rand[0] + F(lookup_table[i][j])*lookup_rand[1]
                + lookup_rand[2]*F(access_table[i][j]) +F(i+3)*lookup_rand[3]);
        }
    }

    vector<tr_tuple> arr = read_tr(); 
    vector<vector<int>> _access_table(access_table.size());
    for(int i = 0; i < _access_table.size(); i++){
        _access_table[i].resize(access_table[i].size(),0);
    }
    F _prod_r = F(1),_prod_w = F(1);
    for(int i = 0; i < arr.size(); i++){
        if(arr[i].type >= 3){
            F v = (arr[i].value_l + F(1)+lookup_rand[0]*arr[i].value_r + lookup_rand[1]*arr[i].value_o+
                            lookup_rand[2]*_access_table[arr[i].type-3][arr[i].value_l.real + 256*arr[i].value_r.real] + lookup_rand[3]*arr[i].type);
            _prod_r *= v;
            r2.push_back((arr[i].value_l + F(1)+lookup_rand[0]*arr[i].value_r + lookup_rand[1]*arr[i].value_o+
                            lookup_rand[2]*_access_table[arr[i].type-3][arr[i].value_l.real + 256*arr[i].value_r.real] + lookup_rand[3]*arr[i].type));
            if(i == 66){
                printf("%d,%d,%d\n",arr[i].type,arr[i].value_l.real,arr[i].value_r.real);    
            }
            _access_table[arr[i].type-3][arr[i].value_l.real + 256*arr[i].value_r.real]++;

            _prod_w *= v + lookup_rand[2];//(arr[i].value_l+ F(1) + lookup_rand[0]*arr[i].value_r + lookup_rand[1]*arr[i].value_o+
                            //lookup_rand[2]*_access_table[arr[i].value_l.real] + lookup_rand[3]*arr[i].type);
        }else if(arr[i].type == 1 || arr[i].type == 2){
            r2.push_back(F(1));
        }
    }
    printf(">> %d,%d,%d\n",r1.size(),r2.size(), arr.size());
    for(int i = 0; i < r2.size(); i++){
        if(r1[i] != r2[i]){
            printf("YY Error %d\n",i);
            exit(-1);
        }
    }
    for(int i = 0; i < _access_table.size(); i++){
        for(int j = 0; j < _access_table[i].size(); j++){
            if(_access_table[i][j] != access_table[i][j]){
                printf("Error %d,%d,%d,%d\n",i,j,_access_table[i][j],access_table[i][j]);
                exit(-1);
            }
        }
    }
    if(prod_r != _prod_r){
        printf("Error 1\n");
    }
    if(prod_w != _prod_w){
        printf("Error 2\n");
    }
    if(_prod_r*prod_f != _prod_w*prod_i){
        printf("Error in lookup test 1\n");
        exit(-1);
    }
}

void test_memory_stream_opt(){
     
    clock_t t1,t2;
      F a = random(),b = random();
  
    t1 = clock();
    _read_tr();
    t2 = clock();
    printf(">> %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
       
    vector<tr_tuple> arr = read_tr();
    int num = 0;
    F _prod_r = F(1),_prod_w = F(1),_prod_i = F(1),_prod_f = F(1);
    vector<vector<int>> acc(circuit_size);
    vector<vector<F>> arr_val(circuit_size);
    vector<F> read_arr;
    for(int i = 0; i < arr.size(); i++){
        if(arr[i].type){
            num++;
            acc[arr[i].idx_l].push_back(arr[i].access_l);
            acc[arr[i].idx_r].push_back(arr[i].access_r);
            acc[arr[i].idx_o].push_back(arr[i].access_o);
            
            arr_val[arr[i].idx_l].push_back(arr[i].value_l);
            arr_val[arr[i].idx_r].push_back(arr[i].value_r);
            arr_val[arr[i].idx_o].push_back(arr[i].value_o);
            
            _prod_r *= (F(arr[i].idx_l) + a*arr[i].value_l + b*F(arr[i].access_l) + F(1));
            _prod_r *= (F(arr[i].idx_r) + a*arr[i].value_r + b*F(arr[i].access_r) + F(1));
            _prod_r *= (F(arr[i].idx_o) + a*arr[i].value_o + b*F(arr[i].access_o) + F(1));
            read_arr.push_back((F(arr[i].idx_l) + a*arr[i].value_l + b*F(arr[i].access_l) + F(1)));
            read_arr.push_back((F(arr[i].idx_r) + a*arr[i].value_r + b*F(arr[i].access_r) + F(1)));
            read_arr.push_back((F(arr[i].idx_o) + a*arr[i].value_o + b*F(arr[i].access_o) + F(1)));
            
            _prod_w *= (F(arr[i].idx_l) + a*arr[i].value_l + b*(F(arr[i].access_l)+F(1)) + F(1));
            _prod_w *= (F(arr[i].idx_r) + a*arr[i].value_r + b*(F(arr[i].access_r)+F(1)) + F(1));
            _prod_w *= (F(arr[i].idx_o) + a*arr[i].value_o + b*(F(arr[i].access_o)+F(1)) + F(1));
        }else{
            acc[arr[i].idx_o].push_back(arr[i].access_o);
            arr_val[arr[i].idx_o].push_back(arr[i].value_o);
            _prod_i *= (F(arr[i].idx_o) + a*arr[i].value_o + F(1));
            _prod_f *= (F(arr[i].idx_o) + a*arr[i].value_o + b*F(arr[i].access_o) + F(1));

        }
    }
    printf("~~~ %d\n",read_arr.size());
    
    vector<tr_tuple> arr2 = read_tr();
    for(int i = 0 ;i < arr2.size(); i++){
        if(arr2[i].value_l != arr[i].value_l){
            printf("Error %d\n",i);
            exit(-1);
        }
    }

    if(_prod_i*_prod_w != _prod_r*_prod_f){
        printf("=== Error\n");
    }

    stream_descriptor fd;fd.name = "wiring_consistency_check_opt"; fd.size = 4*gates;
    reset_stream(fd);
  
    a_w = a; b_w = b;
    vector<F> v(2*BUFFER_SPACE);
    
    F prod_r = F(1),prod_w = F(1),prod_f = F(1),prod_i = F(1);
    float t = 0.0;
    int counter= 0;
    for(int i = 0; i < 3*circuit_size/(BUFFER_SPACE); i++){
        t1 = clock();
        read_stream(fd,v,2*BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_r *= v[j];
            if(counter < read_arr.size() && read_arr[counter++] != v[j]){
                printf("Errror %d,%d\n",i,j);
                exit(-1);
            }
        }

        for(int j = 0; j < BUFFER_SPACE; j++){
            if(v[j] != F(1) && (v[j]+b) != v[j+BUFFER_SPACE]){
                printf("Error %d\n",j);
                exit(-1);
            }
            if(v[j] == F(1) && v[j+BUFFER_SPACE] != F(1)){
                printf(">>Error %d\n",j);
                exit(-1);
            }
            prod_w *= (v[j+BUFFER_SPACE]);
        }
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    printf("OK\n");
    
    for(int i = 0; i < circuit_size/(BUFFER_SPACE); i++){
        t1 = clock();
        read_stream(fd,v,2*BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_i *= v[j];
        }
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_f *= v[j+BUFFER_SPACE];
        }   
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    
    printf(">> %lf\n",t);
  
    
    if(prod_f*prod_r != prod_w*prod_i){
        printf("Memory inconsistency\n");
    }
    //check_correctness();
   
   
    printf(">> %d\n",circuit_size);
    for(int i = 0; i < acc.size(); i++){
        if(acc[i].size()){
            if(acc[i][0] != 0){
                printf("Error %d\n",i);
                for(int j = 0; j < acc[i].size(); j++){
                    printf("%d ",acc[i][j]);
                }
                printf("\n");
                exit(-1);
            }
        for(int j = 1; j < acc[i].size(); j++){
            if(acc[i][j] != acc[i][j-1]+1){
                printf("Error %d,%d\n",i,j);
                for(int k = 0; k < acc[i].size(); k++){
                    printf("%d ",acc[i][k]);
                }
                printf("\n");
                exit(-1);
            }
        }
        }
        
    }
    if(_prod_i != prod_i){
        printf("Errro 1\n");
    }
    if(_prod_f != prod_f){
        printf("Errro 2\n");
    }
    if(_prod_w != prod_w){
        printf("Errro 3\n");
    }
    if(_prod_r != prod_r){
        printf("Errro 4\n");
    }
    
}

void test_memory_stream(){
    
    clock_t t1 = clock();
    Seval();
    clock_t t2 = clock();
    printf("> %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    
    t1 = clock();
    _read_tr();
    t2 = clock();
    printf(">> %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    
    
    stream_descriptor fd;fd.name = "wiring_consistency_check"; fd.size = 8*circuit_size;
    reset_stream(fd);
    /*
    vector<F> buff1(BUFFER_SPACE),buff2(BUFFER_SPACE),buff3(BUFFER_SPACE);
    vector<F> _arr1;
    vector<F> _arr2;
    vector<F> _arr3;
    
    
    
    double t = 0.0;
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
       t1 = clock();
       read_memory(fd,  buff1, buff2, buff3);
       t2 = clock();
       t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
       for(int j  =0; j < buff1.size(); j++){
            _arr1.push_back(buff1[j]);
            _arr2.push_back(buff2[j]);
            _arr3.push_back(buff3[j]);
       }
    }
    printf("%lf\n",t);
    */
    
    F a = random(),b = random();
    a_w = a; b_w = b;
    vector<F> v(BUFFER_SPACE);
    
    F prod_r = F(1),prod_w = F(1),prod_f = F(1),prod_i = F(1);
    float t = 0.0;
    for(int i = 0; i < 3*circuit_size/BUFFER_SPACE; i++){
        t1 = clock();
        read_stream(fd,v,BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_r *= v[j];
        }   
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    for(int i = 0; i < 3*circuit_size/BUFFER_SPACE; i++){
        t1 = clock();
        read_stream(fd,v,BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_w *= v[j];
        }   
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    for(int i = 0; i < circuit_size/BUFFER_SPACE; i++){
        t1 = clock();
        read_stream(fd,v,BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_i *= v[j];
        }   
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    for(int i = 0; i < circuit_size/BUFFER_SPACE; i++){
       t1 = clock();
         read_stream(fd,v,BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j = 0; j < BUFFER_SPACE; j++){
            prod_f *= v[j];
        }   
        //prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    printf(">> %lf\n",t);
    /*
    for(int i = 0; i < 3*circuit_size/BUFFER_SPACE; i++){
        
        prod_r *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    for(int i = 3*circuit_size; i < 6*circuit_size; i++){
        prod_w *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }for(int i = 6*circuit_size; i < 7*circuit_size; i++){
        prod_i *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }for(int i = 7*circuit_size; i < 8*circuit_size; i++){
        prod_f *= (_arr1[i]+a*_arr2[i]+b*_arr3[i]+F(1));
    }
    */
    
    if(prod_f*prod_r != prod_w*prod_i){
        printf("Memory inconsistency\n");
    }
    check_correctness();
    vector<tr_tuple> arr = read_tr();
    F _prod_r = F(1),_prod_w = F(1),_prod_i = F(1),_prod_f = F(1);
    printf("%d\n",arr.size());
    vector<vector<int>> acc(circuit_size);
    for(int i = 0; i < arr.size(); i++){
        if(arr[i].type){
            acc[arr[i].idx_l].push_back(arr[i].access_l);
            acc[arr[i].idx_r].push_back(arr[i].access_r);
            acc[arr[i].idx_o].push_back(arr[i].access_o);
            
            
            _prod_r *= (F(arr[i].idx_l) + a*arr[i].value_l + b*F(arr[i].access_l) + F(1));
            _prod_r *= (F(arr[i].idx_r) + a*arr[i].value_r + b*F(arr[i].access_r) + F(1));
            _prod_r *= (F(arr[i].idx_o) + a*arr[i].value_o + b*F(arr[i].access_o) + F(1));
            _prod_w *= (F(arr[i].idx_l) + a*arr[i].value_l + b*(F(arr[i].access_l)+F(1)) + F(1));
            _prod_w *= (F(arr[i].idx_r) + a*arr[i].value_r + b*(F(arr[i].access_r)+F(1)) + F(1));
            _prod_w *= (F(arr[i].idx_o) + a*arr[i].value_o + b*(F(arr[i].access_o)+F(1)) + F(1));
        }else{
            acc[arr[i].idx_o].push_back(arr[i].access_o);
            
            _prod_i *= (F(arr[i].idx_o) + a*arr[i].value_o + F(1));
            _prod_f *= (F(arr[i].idx_o) + a*arr[i].value_o + b*F(arr[i].access_o) + F(1));

        }
    }
    for(int i = 0; i < acc.size(); i++){
        if(acc[i].size()){
            if(acc[i][0] != 0){
            printf("Error %d\n",i);
            exit(-1);
        }
        for(int j = 1; j < acc[i].size(); j++){
            if(acc[i][j] != acc[i][j-1]+1){
                printf("Error %d\n",i,j);
            }
        }
        }
        
    }
    if(_prod_i != prod_i){
        printf("Errro 1\n");
    }
    if(_prod_f != prod_f){
        printf("Errro 2\n");
    }
    if(_prod_w != prod_w){
        printf("Errro 3\n");
    }
    if(_prod_r != prod_r){
        printf("Errro 4\n");
    }
    if(_prod_i*_prod_w != _prod_r*_prod_f){
        printf("=== Error\n");
    }
}

void test_transcript(){
    stream_descriptor fd;fd.name = "transcript_stream"; fd.size = circuit_size;
    reset_stream(fd);
    
    vector<F> buff_L(BUFFER_SPACE), buff_R(BUFFER_SPACE), buff_O(BUFFER_SPACE);
    vector<int> buff_gate(BUFFER_SPACE);
    vector<F> arr1,arr2;
    clock_t t1,t2;
    double st = 0.0;
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        t1 = clock();
        read_trace(fd, buff_L, buff_R, buff_O, buff_gate);
        t2 = clock();
        st += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        for(int j  = 0; j < BUFFER_SPACE; j++){
            arr1.push_back(buff_L[j]);
            arr1.push_back(buff_R[j]);
            arr1.push_back(buff_O[j]);
            arr1.push_back(buff_gate[j]);
        }
    }
    printf("%lf\n",st);
    reset_stream(fd);
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        read_trace(fd, buff_L, buff_R, buff_O, buff_gate);
        for(int j  = 0; j < BUFFER_SPACE; j++){
            arr2.push_back(buff_L[j]);
            arr2.push_back(buff_R[j]);
            arr2.push_back(buff_O[j]);
            arr2.push_back(buff_gate[j]);
        }
    }
    for(int i = 0; i < arr1.size(); i++){
        if(arr1[i] != arr2[i]){
            printf("Error %d",i);
            exit(-1);
        }
    }
}

void prove_arbitrary_circuit(){
        has_lookups = false;
        stream_descriptor fd1;fd1.name = "transcript_stream"; fd1.size = circuit_size;
        reset_stream(fd1);
        stream_descriptor fd2;fd2.name = "wiring_consistency_check_opt"; fd2.size = 8*circuit_size;
        reset_stream(fd2);
        stream_descriptor fd_witness;fd_witness.name = "witness"; fd_witness.size = 4*circuit_size;
        reset_stream(fd_witness);
        // add gates, accesses, idexes
        stream_descriptor fd_circuit; fd_circuit.name = "circuit";fd_circuit.size = 16*circuit_size;
        reset_stream(fd_circuit);

        _hash comm;
        vector<vector<_hash>> circuit_hashes;
        init_commitment(false);
        //commit(fd_circuit,comm,circuit_hashes);
        reset_stream(fd_circuit);
        vector<F> prev_x;
        double vt = 0.0,ps = 0.0;
        a_w = random(); b_w = random();
        vector<vector<_hash>> MT_hashes;
        clock_t t1,t2;
        clock_t aux_t1,aux_t2;
        t1 = clock();
        init_commitment(false);
        aux_t1 = clock();
        commit(fd_witness,comm,MT_hashes);
        circuit_hashes = MT_hashes;
        aux_t2 = clock();
        printf("Commit time: %lf\n", (double)(aux_t2-aux_t1)/(double)CLOCKS_PER_SEC);
        aux_t1 = clock();
        prove_multiplication_tree_stream_shallow(fd2,8,fd2.size/8, F(32), 5,prev_x,0, vt, ps);
        aux_t2 = clock();
        printf("Wiring Consistency: %lf\n", (double)(aux_t2-aux_t1)/(double)CLOCKS_PER_SEC);
        aux_t1 = clock();
        prove_gate_consistency(fd1, generate_randomness((int)log2(fd1.size)), vt, ps);
        aux_t2 = clock();
        printf("Gate Consistency: %lf\n", (double)(aux_t2-aux_t1)/(double)CLOCKS_PER_SEC);
        aux_t1 = clock();
        open(fd_witness,generate_randomness((int)log2(fd_witness.size)),MT_hashes,vt,ps);
        open(fd_circuit,generate_randomness((int)log2(fd_circuit.size)),circuit_hashes,vt,ps);
        aux_t2 = clock();
        printf("Open: %lf\n", (double)(aux_t2-aux_t1)/(double)CLOCKS_PER_SEC);
        t2 = clock();  
        printf("Pt : %lf, Ps : %lf KB, Vt : %lf, streaming time: %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC,ps,vt,routine_time);    


}


void prove_circuit(){
    if(fun == 1 || fun == 3 || fun == 9){
        has_lookups = false;
        stream_descriptor fd1;fd1.name = "transcript_stream"; fd1.size = circuit_size;
        reset_stream(fd1);
        stream_descriptor fd2;fd2.name = "wiring_consistency_check_opt"; fd2.size = 8*circuit_size;
        reset_stream(fd2);
        stream_descriptor fd_witness;fd_witness.name = "witness"; fd_witness.size = 4*circuit_size;
        reset_stream(fd_witness);

        vector<F> prev_x;
        double vt = 0.0,ps = 0.0;
        a_w = random(); b_w = random();
        vector<vector<_hash>> MT_hashes;
        _hash comm;
        clock_t t1,t2;
        t1 = clock();
        init_commitment(false);
        commit(fd_witness,comm,MT_hashes);
        printf("Prove multree of size : %lld\n",fd2.size);
        prove_multiplication_tree_stream_shallow(fd2,8,fd2.size/8, F(32), 5,prev_x,0, vt, ps);
        prove_gate_consistency(fd1, generate_randomness((int)log2(fd1.size)), vt, ps);
        open(fd_witness,generate_randomness((int)log2(fd_witness.size)),MT_hashes,vt,ps);
        t2 = clock();  
        printf("Pt : %lf, Ps : %lf KB, Vt : %lf, streaming time: %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC,ps,vt,routine_time);    
    }else if(fun == 2 || fun == 5 || fun == 6){
        has_lookups = true;
        stream_descriptor fd1;fd1.name = "transcript_stream"; fd1.size = circuit_size;
        reset_stream(fd1);
        stream_descriptor fd2;fd2.name = "wiring_consistency_check_opt"; fd2.size = 8*circuit_size;
        reset_stream(fd2);
        stream_descriptor fd3;fd3.name = "lookup_basic"; fd3.size = 2*circuit_size;
        reset_stream(fd3);
        stream_descriptor fd_witness;fd_witness.name = "witness"; fd_witness.size = 4*circuit_size;
        reset_stream(fd_witness);
        stream_descriptor fd_witness_lookup;fd_witness_lookup.name = "lookup_witness_basic"; fd_witness_lookup.size = 2*circuit_size;
        reset_stream(fd_witness_lookup);
        
        vector<F> prev_x;
        double vt = 0.0,ps = 0.0;
        a_w = random(); b_w = random();
        vector<vector<_hash>> MT_hashes,MT_hashes_lookup;
        _hash comm;
        clock_t t1,t2;
        t1 = clock();
        
        init_commitment(false);
        commit(fd_witness,comm,MT_hashes);
        lookup_rand = generate_randomness(4);
 
        commit(fd_witness_lookup,comm,MT_hashes_lookup);
        prove_multiplication_tree_stream_shallow(fd2,8,fd2.size/8, F(32), 5,prev_x,0, vt, ps);
        vector<F> prods = prove_multiplication_tree_stream_shallow(fd3,2,fd3.size/2, F(32), 5,prev_x,0, vt, ps);
        prove_gate_consistency_lookups(fd1, generate_randomness((int)log2(fd1.size)), vt, ps);
        open(fd_witness,generate_randomness((int)log2(fd_witness.size)),MT_hashes,vt,ps);
        open(fd_witness_lookup,generate_randomness((int)log2(fd_witness_lookup.size)),MT_hashes_lookup,vt,ps);
        t2 = clock();  
        double pt = (double)(t2-t1)/(double)CLOCKS_PER_SEC;
        
        
        t1 = clock();
    
    
        F prod_i = F(1),prod_f = F(1);
        for(int j = 0; j < access_table[0].size(); j++){
            prod_i *= (F(j) +F(1)+ F(lookup_table[0][j])*lookup_rand[1]+F(3)*lookup_rand[3]);
            prod_f *= (F(j) +F(1)+ F(lookup_table[0][j])*lookup_rand[1] + lookup_rand[2]*F(access_table[0][j]) +F(3)*lookup_rand[3]);
        }


        for(int i = 1; i < access_table.size(); i++){
            for(int j = 0; j < access_table[i].size(); j++){
                int idx1 = j%256;
                int idx2 = j>>8;
                
                prod_i *= (F(idx1)+ F(1) + F(idx2)*lookup_rand[0] + F(lookup_table[i][j])*lookup_rand[1]
                    +F(i+3)*lookup_rand[3]);
                prod_f *= (F(idx1) + F(1)+ F(idx2)*lookup_rand[0] + F(lookup_table[i][j])*lookup_rand[1]
                    + lookup_rand[2]*F(access_table[i][j]) +F(i+3)*lookup_rand[3]);
            }
        }
        t2 = clock();
        printf("Pt : %lf, Ps : %lf KB, Vt : %lf, streaming time: %lf\n",pt,ps,vt+((double)(t2-t1)/(double)CLOCKS_PER_SEC),routine_time);    
        if(prods[0]*prod_f != prods[1]*prod_i){
            printf(">> Error\n");
            exit(-1);
        }else{
            printf("OK\n");
        }
    }  
       
}

void test_witness_stream(){
    stream_descriptor fd;fd.name = "witness"; fd.size = circuit_size;
    reset_stream(fd);
    vector<F> witness1(4*circuit_size),witness2(4*circuit_size);
    vector<F> buff(BUFFER_SPACE);
    clock_t t1 = clock();
    for(int i  = 0; i < 4*circuit_size/BUFFER_SPACE; i++){
        read_stream(fd,buff,BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            witness1[i*BUFFER_SPACE+j] = buff[j];
        }
    }
    clock_t t2 = clock();
    printf("%lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
       
    for(int i  = 0; i < 4*circuit_size/BUFFER_SPACE; i++){
        read_stream(fd,buff,BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            witness2[i*BUFFER_SPACE+j] = buff[j];
        }
    }   
    for(int i  =0; i < witness1.size(); i++){
        if(witness1[i] != witness2[i]){
            printf("Error %d\n",i);
            exit(-1);
        }
    }
}


void prove_circuit_standard(){
    stream_descriptor fd1;fd1.name = "transcript_stream"; fd1.size = circuit_size;
    reset_stream(fd1);
    stream_descriptor fd2;fd2.name = "wiring_consistency_check"; fd2.size = 8*circuit_size;
    reset_stream(fd2);
    
    
    

    clock_t t1,t2;
    t1 = clock();
    vector<F> circuit_poly(16*circuit_size,F(0));
    vector<F> buff_L(BUFFER_SPACE), buff_R(BUFFER_SPACE), buff_O(BUFFER_SPACE);
    vector<int> buff_gate(BUFFER_SPACE);
    vector<F> arr_L(fd1.size,F(0)),arr_R(fd1.size,F(0)),arr_O(fd1.size,F(0)),arr_gate(fd1.size,F(0));
    int counter = 0;
    for(int i = 0; i < fd1.size/BUFFER_SPACE; i++){
        read_trace(fd1, buff_L, buff_R, buff_O, buff_gate);
        for(int j  = 0; j < BUFFER_SPACE; j++){
            arr_L[BUFFER_SPACE*i + j] = buff_L[j];
            arr_R[BUFFER_SPACE*i + j] = buff_R[j];
            arr_O[BUFFER_SPACE*i + j] = buff_O[j];
            arr_gate[BUFFER_SPACE*i + j] = buff_gate[j];
            circuit_poly[counter++] = buff_gate[j];
        }
    }
        
    vector<F> buff_addr(BUFFER_SPACE),buff_value(BUFFER_SPACE),buff_access(BUFFER_SPACE);
    vector<F> addr(fd2.size),value(fd2.size),access(fd2.size);
    vector<vector<F>> mul_tree_input(8);
    double vt =0.0, ps = 0.0;
    vector<F> prev_x;
    for(int i = 0; i < 8; i++){
        mul_tree_input[i].resize(fd2.size/8);
    }
    F a = random(),b = random();
    addresses = new int[3*BUFFER_SPACE_tr];
    values = new F[3*BUFFER_SPACE_tr];
    accesses = new int[3*BUFFER_SPACE_tr];
    types = new uint8_t[3*BUFFER_SPACE_tr];

    for(int i = 0; i < fd2.size/BUFFER_SPACE; i++){
        read_memory(fd2,  buff_addr, buff_value, buff_access);
        for(int j = 0; j < BUFFER_SPACE; j++){
            addr[BUFFER_SPACE*i + j] = buff_addr[j];
            value[BUFFER_SPACE*i + j] = buff_value[j];
            access[BUFFER_SPACE*i + j] = buff_access[j];
            if(i < fd2.size/(2*BUFFER_SPACE)){
                circuit_poly[counter++] = buff_addr[j];
                circuit_poly[counter++] = buff_access[j];
            }
        }
    }
    
    for(int i = 0; i  < 8; i++){
        for(int j = 0; j < mul_tree_input[i].size(); j++){
            mul_tree_input[i][j] = addr[i*mul_tree_input[i].size() + j] + a*value[i*mul_tree_input[i].size() + j] 
            + b*access[i*mul_tree_input[i].size() + j] + F(1);
        }
    }
    
    t2 = clock();
    double pt = 0;
    pt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    vector<vector<_hash>> circuit_hashes;
    vector<vector<vector<F>>> circuit_tensor;
    _hash comm;
    linear_time = false;
    tensor_row_size = 128;
    
    commit_standard(circuit_poly ,comm, circuit_hashes,circuit_tensor, 32);
    //circuit_poly.clear();
    //vector<F>(circuit_poly).swap(circuit_poly);
    tensor_row_size = 4*circuit_size/(32*1ULL<<(11));
    expander_init_store(tensor_row_size);
        
    t1 = clock(); 
    vector<F> witness(4*circuit_size,F(0));
    counter = 0;
    for(int i = 0; i < arr_O.size(); i++){
        witness[counter++] = arr_L[i];
        witness[counter++] = arr_R[i];
        witness[counter++] = arr_O[i];
    }
    for(int i = 0; i < circuit_size; i++){
        witness[counter++] = value[value.size()-circuit_size+i];
    }

    vector<vector<vector<F>>> witness_tensor;
    vector<vector<_hash>> witness_hashes;
    linear_time = true;
    commit_standard(witness ,comm, witness_hashes,witness_tensor, 32);
    prove_multiplication_tree_new(mul_tree_input,F(322),prev_x,vt,ps);
    prove_gate_consistency_standard(arr_L,arr_R,arr_O,arr_gate,generate_randomness((int)log2(arr_L.size())),vt,ps);
    open_standard(witness, generate_randomness((int)log2(4*circuit_size)),  witness_hashes,witness_tensor ,32, vt,ps);
    linear_time = false;
    tensor_row_size = 128;
    open_standard(circuit_poly, generate_randomness((int)log2(16*circuit_size)),  circuit_hashes,circuit_tensor ,32, vt,ps);
    t2 = clock();
    pt+= (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    
    printf("Pt : %lf, Vt : %lf, Ps : %lf\n",pt,vt,ps);
}

void init_stream(int b, int n, int d){
    input_size = 1ULL<<(n);
    depth = d;
    BUFFER_SPACE = 1ULL<<(b);
    if(BUFFER_SPACE > input_size*128){
        BUFFER_SPACE = input_size*128;
    }
    BUFFER_SPACE_tr =  1ULL<<((int)log2(BUFFER_SPACE)-3);
    tr = new tr_tuple[BUFFER_SPACE_tr];

    circuit_size = get_circuit_size();
    printf("%d\n",circuit_size);
    gates = circuit_size;
    ops = circuit_size;
    has_lookups = false;
    if(fun == 2 || fun == 4){
        has_lookups = true;
    }
    if(1ULL<<((int)log2(gates)) != gates){
        gates = 1ULL<<(1+(int)log2(gates));
    }
    if(1ULL<<((int)log2(ops)) != ops){
        ops = 1ULL<<(1+(int)log2(ops));
    }
    // later see if we can do better
    ops = gates;
    
}

F _eq(vector<F> r1, vector<F> r2, int i){
    F y = F(1);
    //for(int j = 0; j < r1.size()-i; j++){
    for(int j = i; j < r1.size(); j++){
        printf("OK\n");
        y *= ((r1[j]*r2[j]) + (F(1)- r1[j])*(F(1)-r2[j]));
    }
    return y;
}

void test_next(){
    vector<F> beta1,beta2;
    vector<F> r1 = generate_randomness(10);
    vector<F> r2 = generate_randomness(10);
    precompute_beta(r1,beta1);
    precompute_beta(r2,beta2);
    vector<F> poly(1ULL<<(r1.size()),F(0));
    for(int i = 1 ; i < poly.size(); i++){
        poly[i-1] = beta1[i];
    }
   
    vector<F> y(r1.size(),F(1));
    F y1 = F(1);
    for(int i = 0; i < r1.size(); i++){
        //y[i-1] = (F(1)-r1[r1.size()-i])*(r2[r1.size()-i])*_eq(r1,r2,i);
        if(i != r1.size()-1){
            y[i] = (F(1)-r2[i])*(r1[i])*_eq(r1,r2,i+1);
        }else{
            y[i] =  (F(1)-r2[i])*(r1[i]);
        }

        if(i > 0){
            y1 *= (F(1)-r1[i-1])*(r2[i-1]);
        }
        y[i]*= y1;
    }
    F final_y = y[0];
    for(int i = 1; i < y.size(); i++){
        if(y[i] == F(1)){
            printf("Err\n");
        }
        final_y += y[i];
    }
    for(int i = 0; i < poly.size(); i++){
        final_y -= beta2[i]*poly[i];
    }
    if(final_y != 0){
    //if(final_y != evaluate_vector(poly,r2)){
        printf("Error\n");
    }
}


int main(int argc, char *argv[]){
    init_hash();
    mtx.lock();
    mtx2.lock();
    
    //test_PC(1ULL<<(atoi(argv[1])),atoi(argv[2]),atoi(argv[3]));
    //BUFFER_SPACE = 1ULL<<(atoi(argv[2]));
    //test_Elastic_PC(1ULL<<(atoi(argv[1])), atoi(argv[3]));
    //exit(-1);
    
    
    if(atoi(argv[1]) == 0){
        fun = atoi(argv[2]);
        thread t(Seval_Oracle);
        if(fun == 8){
            prune_rate = (atoi(argv[6]))/100.0;
            printf("Prune rate: %lf\n",prune_rate);
        }else if(fun == 9){
            int lsize = atoi(argv[6]);
            for(int i = 0; i < lsize; i++){
                layer_size.push_back(atoi(argv[6+i]));
            }
        }
        
        init_stream(atoi(argv[3]),atoi(argv[4]),atoi(argv[5]));
      
        check_correctness();
        printf("%d\n", circuit_size);
        t.detach();
        //sleep(10);
    
    }else if(atoi(argv[1]) == 11){
        fun = 1;
        thread t(Seval_Oracle);
        init_stream(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
        prove_circuit_standard();
        t.detach();
    
    }
    else{
        fun = atoi(argv[1]);
        if(fun == 8){
            prune_rate = (double)atoi(argv[5])/100.0;
        }else if(fun == 9){
            int lsize = atoi(argv[5]);
            for(int i = 0; i < lsize; i++){
                layer_size.push_back(atoi(argv[6+i]));
            }
        }
        thread t(Seval_Oracle);
        init_stream(atoi(argv[2]),atoi(argv[3]),atoi(argv[4]));
        double vt = 0.0,ps = 0.0;
        a_w = random(); b_w = random();
        printf("Cir size: %d\n",circuit_size);
        clock_t t1,t2;
        if(fun == 1 || fun == 7){
            prove_arbitrary_circuit();
        }else if(fun == 8){
            prove_arbitrary_circuit();
        }else{
            prove_circuit();            
        }
        t.detach();
    
    }
    return 0;
}
