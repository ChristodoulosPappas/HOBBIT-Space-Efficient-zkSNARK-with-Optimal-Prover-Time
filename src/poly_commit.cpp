#include "expanders.h"
#include "linear_code_encode.h"
#include <math.h>
#include "poly_commit.h"
#include "utils.hpp"
#include "Kopis.h"
#include "Virgo.h"
#include "sumcheck.h"

#define QUERIES_LE 3000
#define QUERIES_RS 150
int row_size = 6; 


extern int PC_scheme,Commitment_hash;
extern bool __encode_initialized;
extern double proving_time;
vector<F> _w;


void precompute_omegas(int logn){
    _w.clear();
    _w.resize(1ULL<<logn);

    _w[0] = F_ONE;

    // Get root of unity
    F rou;
    rou = 1033321771269002680L;
    //rou.real = 2147483648L;

    
    
    for (int i = 0; i < 62 - logn; ++i)
        rou = rou * rou;

    _w[1] = rou;
    
    for (u32 i = 2; i < (1ULL<<logn); ++i) _w[i] = _w[i - 1] * _w[1];
    
    
   
}

void my_fft(vector<F> &arr, int logn, bool flag) {
//    cerr << "fft: " << endl;
//    for (auto x: arr) cerr << x << ' ';
//    cerr << endl;
    static std::vector<u32> rev;
    static std::vector<F> _w;

    u32 len = 1ULL << logn;
    assert(arr.size() == len);

    rev.resize(len);
    _w.resize(len);

    rev[0] = 0;
    for (u32 i = 1; i < len; ++i)
        rev[i] = rev[i >> 1] >> 1 | (i & 1) << (logn - 1);

    
    if (flag) _w[1] = _w[1].inv();
    
    
    for (u32 i = 0; i < len; ++i)
        if (rev[i] < i) std::swap(arr[i], arr[rev[i]]);

    for (u32 i = 2; i <= len; i <<= 1)
        for (u32 j = 0; j < len; j += i)
            for (u32 k = 0; k < (i >> 1); ++k) {
                auto u = arr[j + k];
                auto v = arr[j + k + (i >> 1)] * _w[len / i * k];
                arr[j + k] = u + v;
                arr[j + k + (i >> 1)] = u - v;
    
            }

    if (flag) {
        F ilen;
        ilen = F(len).inv();//ilen, len);
        for (u32 i = 0; i < len; ++i){
            arr[i] = arr[i] * ilen;
    
        }
    }
}



void test( vector<vector<F>> &matrix, commitment &comm,int bit_col, int bit_row){
    for(int i = 0; i < 1ULL<<(bit_row+1); i++){
        for(int j = 0;  j < 1ULL<<(bit_col+1); j++){
            matrix[i][j] = matrix[i][j] + F_ONE;

        }
    }
}






void Pigeon_breakdown_gen(Pigeon_breakdown_pp &pp){
}

void Pigeon_breakdown_commit_stream(stream_descriptor fd , __hhash_digest &comm, vector<vector<__hhash_digest>> &MT_hashes){
    int bit_size = (int)log2(fd.size);
    int bit_row,bit_col;
    vector<F> arr;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    bit_row -= row_size;
    bit_col += row_size;
    
    
    vector<F> buff(1ULL<<(bit_col));
    vector<vector<F>> encoded_buff(4);
    for(int i = 0; i < encoded_buff.size();i++){
        encoded_buff[i].resize((1ULL<<(bit_col+1)),F(0));
    }
    
    int counter= 0;
    vector<__hhash_digest> buff_hash(1ULL<<(bit_col+1));
    expander_init(1ULL<<(bit_col));
    for(int i = 0; i < buff_hash.size(); i++){
        memset(&buff_hash[i], 0, sizeof(__hhash_digest));
    }
    for(int i = 0; i < fd.size/(1ULL<<(bit_col)); i++){
        read_stream(fd,buff,buff.size());
        encode(buff.data(),encoded_buff[i%4].data(),buff.size());
        if(i != 0 && i%4 == 0){
            for(int j = 0; j < encoded_buff[0].size(); j++){
                buff_hash[j] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_buff[0][j],encoded_buff[1][j],encoded_buff[2][j],encoded_buff[3][j], buff_hash[j]);
            }
        }
    }
    if(fd.size/(1ULL<<(bit_col)) < 4){
        for(int j = 0; j < encoded_buff[0].size(); j++){
            buff_hash[j] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_buff[0][j],encoded_buff[1][j],encoded_buff[2][j],encoded_buff[3][j], buff_hash[j]);
        }    
    }
    
    
    
    MT_hashes.resize((int)log2(buff.size())+1);
    MT_hashes[0] = buff_hash;
    merkle_tree::merkle_tree_prover::create_tree( buff.size() , MT_hashes, sizeof(__hhash_digest), true);
    
}


poly_proof Pigeon_breakdown_open_stream(stream_descriptor fd, vector<F> x){
    poly_proof P;
    
    return P;
}

vector<vector<F>> Pigeon_breakdown_commit(vector<F> poly , __hhash_digest &comm, vector<vector<__hhash_digest>> &MT_hashes){
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    vector<F> arr;
    vector<vector<F>> temp_matrix,encoded_matrix;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }
    if(9 >= bit_row){
        printf("Small polynomial\n");
        vector<vector<__hhash_digest>> hash_tree;
        encoded_matrix.clear();
        encoded_matrix.resize(1);
        
        Virgo_commit(poly, encoded_matrix[0], hash_tree, 16);
        return encoded_matrix;
    }

    bit_row -= row_size;
    bit_col += row_size;
    
    encoded_matrix.resize(1ULL<<(bit_row));
    expander_init_store(1ULL<<(bit_col));

    clock_t t1,t2;
    t1 = clock();
    vector<F> temp(1ULL<<(bit_col));
    int counter= 0;
    
    for(int i = 0; i < encoded_matrix.size(); i++){
        encoded_matrix[i].resize(1ULL<<(bit_col + 1),F_ZERO);
        for(int j = 0; j < encoded_matrix[i].size()/2; j++){
            temp[j] = poly[counter++];
        }
        encode_monolithic(temp.data(),encoded_matrix[i].data(),temp.size());
    }
    
    vector<__hhash_digest> buff(encoded_matrix[0].size());
    for(int i = 0; i < buff.size(); i++){
        memset(&buff[i], 0, sizeof(__hhash_digest));
    }
    for(int j = 0; j < encoded_matrix.size()/4; j+=1){
        for(int i = 0; i < encoded_matrix[0].size(); i++){
            buff[i] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_matrix[4*j][i], encoded_matrix[4*j+1][i],encoded_matrix[4*j+2][i],encoded_matrix[4*j+3][i], buff[i]);
        }
    }
    printf("%d,%d\n",bit_col,bit_row);
    
    MT_hashes.resize((int)log2(buff.size())+1);
    MT_hashes[0] = buff;
    merkle_tree::merkle_tree_prover::create_tree( buff.size() , MT_hashes, sizeof(__hhash_digest), true);
    //Virgo_commit();
    //MIPP_commit_stream(h,h.size(),pp.pp_pc,pp.commitments);
    
    t2 = clock();
    proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;    
    //merkle_tree::merkle_tree_prover::create_tree( buff.size() , buff, sizeof(__hhash_digest), true);
    return encoded_matrix;
    
}

poly_proof Pigeon_breakdown_open(vector<F> &poly , vector<vector<F>> &encoded_matrix, vector<F> x){
    poly_proof P;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    if(9 >= bit_row){
        printf("Small polynomial\n");
        //Virgo_open(poly,poly.size(),x,pp.pp_pc,pp.commitments,16);
        return P;
    }

    bit_row -= row_size;
    bit_col += row_size;
    

    F r = F(rand());
    vector<F> r_vec(1ULL<<(bit_row));
    r_vec[0] = r;
    for(int i = 1; i < 1ULL<<(bit_row); i++){
        r_vec[i] = r_vec[i-1]*r_vec[0];
    }

    vector<F> beta1,x1,x2;
    for(int i = 0; i < bit_row; i++){
        x1.push_back(x[i]);
    }
    for(int i = bit_row; i < x.size(); i++){
        x2.push_back(x[i]);
    }  
    precompute_beta(x1,beta1);

    vector<F> challenge_vector(1ULL<<bit_col,F(0)),tensor(1ULL<<bit_col,F(0));
    for(int i = 0; i < 1ULL<<bit_col; i++){
        for(int j = 0; j < 1ULL<<bit_row; j++){
            challenge_vector[i] += r_vec[j]*encoded_matrix[j][i];
            tensor[i] += beta1[j]*encoded_matrix[j][i];
        }
    }
    P.r = r;
    P.tensor = tensor;
    P.challenge_vector = challenge_vector;
    
    vector<F> virgo_tensor,virgo_challenge_vector;
    vector<vector<__hhash_digest>> tensor_hashes,challenge_vector_hashes;
    Virgo_commit(tensor,virgo_tensor,tensor_hashes,16);
    Virgo_commit(challenge_vector,virgo_challenge_vector,challenge_vector_hashes,16);
    
    //MIPP_commit_stream(tensor,tensor.size(),pp.pp_pc,pp.commitments_tensor);
    //MIPP_commit_stream(challenge_vector,challenge_vector.size(),pp.pp_pc,pp.commitments_challenge);
    
    
    
    F a; a = F(rand());
    vector<F> aggr_arr(challenge_vector.size());
    for(int i = 0; i < challenge_vector.size(); i++){
        aggr_arr[i] = tensor[i] + a*challenge_vector[i];
    }    
    
    // Aggregate
    // prove_encoding
    F zero = F(0);
    vector<F> encoded_arr(2*aggr_arr.size());
    encoding_transcript T;
    //generate_encoding_transcript(T ,aggr_arr.data(),encoded_arr.data() ,aggr_arr.size(),0);
    encoded_arr.erase(encoded_arr.begin(),encoded_arr.begin()+aggr_arr.size());
    vector<F> virgo_encoded_arr;
    vector<vector<__hhash_digest>> encoded_arr_hashes;
    Virgo_commit(encoded_arr,virgo_encoded_arr,encoded_arr_hashes,16);
    //prove_linear_code(aggr_arr, T, aggr_arr.size());
    double vt = 0.0,ps = 0.0;
    proof P_mem = prove_membership(aggr_arr,encoded_arr,vt,ps );
    
    F b; b = F(rand());
    vector<F> final_virgo_encoding(virgo_challenge_vector.size());
    for(int i = 0; i < final_virgo_encoding.size(); i++){
        final_virgo_encoding[i] = virgo_tensor[i] + a*virgo_challenge_vector[i] + b*virgo_encoded_arr[i];
    }
    vector<vector<__hhash_digest>> final_hashes;
    MT_commit(final_virgo_encoding, final_hashes, 16);
    vector<MT_proof> paths;
    vector<vector<F>> query_points(4*150);
    for(int i = 0; i < 150; i++){
        paths.push_back(MT_Open(i,final_hashes));
        for(int j = 0; j < 16; j++)query_points[4*i].push_back(final_virgo_encoding[16*i + j]);
        paths.push_back(MT_Open(i,encoded_arr_hashes));
        for(int j = 0; j < 16; j++)query_points[4*i+1].push_back(virgo_encoded_arr[16*i + j]);
        paths.push_back(MT_Open(i,tensor_hashes));
        for(int j = 0; j < 16; j++)query_points[4*i+2].push_back(virgo_tensor[16*i + j]);
        paths.push_back(MT_Open(i,challenge_vector_hashes));
        for(int j = 0; j < 16; j++)query_points[4*i+3].push_back(virgo_challenge_vector[16*i + j]);
    }
    
    Virgo_proof P_open = Virgo_open(aggr_arr,final_virgo_encoding,final_hashes,generate_randomness(x2.size()),16);
    
    if(QUERIES_LE >= encoded_matrix[0].size()){
        P.collumns = encoded_matrix;

    }else{
        P.collumns.resize(encoded_matrix.size());
        for(int i = 0; i < encoded_matrix.size(); i++){
            P.collumns[i].resize(QUERIES_LE);
        }
        for(int i = 0; i < QUERIES_LE; i++){
            for(int j = 0; j < encoded_matrix.size(); j++){
                P.collumns[j][i] = encoded_matrix[j][i];
            }
        }
    }
    P.y = evaluate_vector(tensor,x2);    
    P.P_open = P_open;
    P.paths = paths;
    P.query_points = query_points;
    return P;
}

vector<vector<F>> FFT_breakdown_commit(vector<F> poly, __hhash_digest &comm, vector<__hhash_digest> &leaves){
    //__hhash_digest *mt;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    vector<F> arr;
    vector<vector<F>> temp_matrix,encoded_matrix;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    bit_col += 3;
    bit_row -= 3;
    
    encoded_matrix.resize(1ULL<<(bit_row));
    
    
    clock_t t1,t2;
    t1 = clock();
    //vector<F> temp(1ULL<<(bit_col));
    int counter= 0;
    for(int i = 0; i < encoded_matrix.size(); i++){
        encoded_matrix[i].resize(1ULL<<(bit_col + 1),F_ZERO);
        for(int j = 0; j < encoded_matrix[i].size()/2; j++){
            encoded_matrix[i][j] = poly[counter++];
            //temp[j] = poly[counter++];
        }
        fft(encoded_matrix[i],bit_col+1,false);
        //encode(temp.data(),encoded_matrix[i].data(),temp.size());
    }
    
    vector<__hhash_digest> buff(encoded_matrix[0].size());
    for(int i = 0; i < buff.size(); i++){
        memset(&buff[i], 0, sizeof(__hhash_digest));
    }
    for(int j = 0; j < encoded_matrix.size()/4; j+=1){
        for(int i = 0; i < encoded_matrix[0].size(); i++){
            
            buff[i] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_matrix[4*j][i], encoded_matrix[4*j+1][i],encoded_matrix[4*j+2][i],encoded_matrix[4*j+3][i], buff[i]);
        }
    }
    printf("%d,%d\n",bit_col,bit_row);
    
    t2 = clock();
    proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    
    //merkle_tree::merkle_tree_prover::create_tree( buff.size() , buff, sizeof(__hhash_digest), true);
   
    return encoded_matrix;
    //encoded_matrix.clear();
    //encoded_matrix = vector<vector<F>>();
}

poly_proof FFT_breakdown_open(vector<F> &poly, vector<vector<F>> &encoded_matrix, vector<F> x){
    poly_proof P;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    bit_col += 3;
    bit_row -= 3;
    
    F r = F(rand());
    vector<F> r_vec(1ULL<<(bit_row));
    r_vec[0] = r;
    for(int i = 1; i < 1ULL<<(bit_row); i++){
        r_vec[i] = r_vec[i-1]*r_vec[0];
    }

    vector<F> beta1,x1,x2;
    for(int i = 0; i < bit_row; i++){
        x1.push_back(x[i]);
    }
    for(int i = bit_row; i < x.size(); i++){
        x2.push_back(x[i]);
    }  
    precompute_beta(x1,beta1);

    vector<F> challenge_vector(1ULL<<bit_col,F(0)),tensor(1ULL<<bit_col,F(0));
    for(int i = 0; i < 1ULL<<bit_col; i++){
        for(int j = 0; j < 1ULL<<bit_row; j++){
            challenge_vector[i] += r_vec[j]*encoded_matrix[j][i];
            tensor[i] += beta1[j]*encoded_matrix[j][i];
        }
    }
    P.r = r;
    P.tensor = tensor;
    P.challenge_vector = challenge_vector;
    printf("Encoded matrix: %d,%d\n",encoded_matrix.size(),encoded_matrix[0].size());
    if(150 >= encoded_matrix[0].size()){
        P.collumns = encoded_matrix;

    }else{
        P.collumns.resize(encoded_matrix.size());
        for(int i = 0; i < encoded_matrix.size(); i++){
            P.collumns[i].resize(150);
        }
        for(int i = 0; i < 150; i++){
            for(int j = 0; j < encoded_matrix.size(); j++){
                P.collumns[j][i] = encoded_matrix[j][i];
            }
        }
    }
    P.y = evaluate_vector(tensor,x2);    
    return P;
}



vector<vector<F>> naive_breakdown_commit(vector<F> poly, __hhash_digest &comm, vector<__hhash_digest> &leaves){
    //__hhash_digest *mt;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    vector<F> arr;
    vector<vector<F>> temp_matrix,encoded_matrix;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    bit_col += 10;
    bit_row -= 10;
    
    
    encoded_matrix.resize(1ULL<<(bit_row));
    
    
    clock_t t1,t2;
    t1 = clock();
    vector<F> temp(1ULL<<(bit_col));
    int counter= 0;
    for(int i = 0; i < encoded_matrix.size(); i++){
        encoded_matrix[i].resize(1ULL<<(bit_col + 1),F_ZERO);
        for(int j = 0; j < encoded_matrix[i].size()/2; j++){
            temp[j] = poly[counter++];
        }
        encode_monolithic(temp.data(),encoded_matrix[i].data(),temp.size());
    }
    
    vector<__hhash_digest> buff(encoded_matrix[0].size());
    for(int i = 0; i < buff.size(); i++){
        memset(&buff[i], 0, sizeof(__hhash_digest));
    }
    for(int j = 0; j < encoded_matrix.size()/4; j+=1){
        for(int i = 0; i < encoded_matrix[0].size(); i++){
            buff[i] = merkle_tree::hash_double_field_element_merkle_damgard(encoded_matrix[4*j][i], encoded_matrix[4*j+1][i],encoded_matrix[4*j+2][i],encoded_matrix[4*j+3][i], buff[i]);
        }
    }
    printf("%d,%d\n",bit_col,bit_row);
    
    t2 = clock();
    proving_time += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    
    //merkle_tree::merkle_tree_prover::create_tree( buff.size() , buff, sizeof(__hhash_digest), true);
   
    return encoded_matrix;
    //encoded_matrix.clear();
    //encoded_matrix = vector<vector<F>>();
}

poly_proof naive_breakdown_open(vector<F> &poly, vector<vector<F>> &encoded_matrix, vector<F> x){
    poly_proof P;
    int bit_size = (int)log2(poly.size());
    int bit_row,bit_col;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }

    bit_col += 10;
    bit_row -= 10;
    
    F r = F(rand());
    vector<F> r_vec(1ULL<<(bit_row));
    r_vec[0] = r;
    for(int i = 1; i < 1ULL<<(bit_row); i++){
        r_vec[i] = r_vec[i-1]*r_vec[0];
    }

    vector<F> beta1,x1,x2;
    for(int i = 0; i < bit_row; i++){
        x1.push_back(x[i]);
    }
    for(int i = bit_row; i < x.size(); i++){
        x2.push_back(x[i]);
    }  
    precompute_beta(x1,beta1);

    vector<F> challenge_vector(1ULL<<bit_col,F(0)),tensor(1ULL<<bit_col,F(0));
    for(int i = 0; i < 1ULL<<bit_col; i++){
        for(int j = 0; j < 1ULL<<bit_row; j++){
            challenge_vector[i] += r_vec[j]*encoded_matrix[j][i];
            tensor[i] += beta1[j]*encoded_matrix[j][i];
        }
    }
    P.r = r;
    P.tensor = tensor;
    P.challenge_vector = challenge_vector;
    printf("Encoded matrix: %d,%d\n",encoded_matrix.size(),encoded_matrix[0].size());
    if(QUERIES_LE >= encoded_matrix[0].size()){
        P.collumns = encoded_matrix;

    }else{
        P.collumns.resize(encoded_matrix.size());
        for(int i = 0; i < encoded_matrix.size(); i++){
            P.collumns[i].resize(QUERIES_LE);
        }
        for(int i = 0; i < QUERIES_LE; i++){
            for(int j = 0; j < encoded_matrix.size(); j++){
                P.collumns[j][i] = encoded_matrix[j][i];
            }
        }
    }
    P.y = evaluate_vector(tensor,x2);    
    return P;
}


void naive_breakdown_verify(poly_proof P, vector<F> x){
    int bit_size = x.size();
    int bit_row,bit_col;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }
    bit_col += 10;
    bit_row -= 10;
    
    F r = P.r;
    vector<F> r_vec(1ULL<<(bit_row));
    r_vec[0] = r;
    for(int i = 1; i < 1ULL<<(bit_row); i++){
        r_vec[i] = r_vec[i-1]*r_vec[0];
    }
    vector<F> beta1,x1,x2;
    for(int i = 0; i < bit_row; i++){
        x1.push_back(x[i]);
    }
    for(int i = bit_row; i < x.size(); i++){
        x2.push_back(x[i]);
    }  
    precompute_beta(x1,beta1);
    
    vector<F> encoded_tensor(2*P.tensor.size());
    vector<F> encoded_challenge_vector(2*P.challenge_vector.size());
    
    encode_monolithic(P.tensor.data(),encoded_tensor.data(),P.tensor.size());
    encode_monolithic(P.challenge_vector.data(),encoded_challenge_vector.data(),P.challenge_vector.size());

    for(int j = 0; j < P.collumns[0].size(); j++){
        F sum1 = F_ZERO,sum2 = F_ZERO;
        //printf("%d,%d,%d\n",P.collumns.size(),beta1.size(),j);
        for(int i = 0; i < P.collumns.size(); i++){
            sum1 += P.collumns[i][j]*r_vec[i];
            sum2 += P.collumns[i][j]*beta1[i];
        }
        if(encoded_challenge_vector[j] != sum1){
            printf("Error1 %d\n",j);exit(-1);
        }if(encoded_tensor[j] != sum2){
            printf("Error\n");exit(-1);
        }
    }
     
    if(P.y != evaluate_vector(P.tensor,x2)){
        printf("Error in y\n");
    }
    
    vector<__hhash_digest> buff(P.collumns[0].size());
    for(int i = 0; i < buff.size(); i++){
        memset(&buff[i], 0, sizeof(__hhash_digest));
    }
    for(int j = 0; j < P.collumns.size()/4; j+=1){
        for(int i = 0; i < P.collumns[0].size(); i++){
            buff[i] = merkle_tree::hash_double_field_element_merkle_damgard(P.collumns[4*j][i],P.collumns[4*j+1][i],P.collumns[4*j+2][i],P.collumns[4*j+3][i], buff[i]);
        }
    }

}


void test_naive_brakedown(unsigned long long int size){

    vector<F> arr = generate_randomness(size);
    vector<F> x = generate_randomness((int)log2(size));    
    
    vector<__hhash_digest> leaves;
    __hhash_digest comm;
    int bit_size = x.size();
    int bit_row,bit_col;
    
    if(bit_size%2){
        bit_row = (bit_size+1)/2;
        bit_col = (bit_size-1)/2;
    }else{
        bit_row = (bit_size)/2;
        bit_col = (bit_size)/2;
    }
    bit_col += 10;
    bit_row -= 10;
    expander_init_store(1ULL<<(bit_col));

    printf("Committing\n");
    vector<vector<F>> encoded_poly = naive_breakdown_commit(arr,comm,leaves);
    printf("proving time : %lf \n",proving_time);
    clock_t t1,t2;
    t1 = clock();
    poly_proof P = naive_breakdown_open(arr, encoded_poly, x);
    t2 = clock();
    printf("Open time : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    printf("%d,%d\n",P.challenge_vector.size(),P.collumns.size(),P.collumns[0].size());
    printf("%d,%d\n",P.collumns.size(),P.collumns[0].size());
    printf("Proof size: %lf MB\n",(8.0*(P.challenge_vector.size() + P.tensor.size() + P.collumns.size()*P.collumns[0].size()))/(1024.0*1024.0));
    t1 = clock();
    naive_breakdown_verify(P,x);
    t2 = clock();
    printf("Verification time : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
}


void test_FFT_brakedown(unsigned long long int size){

    vector<F> arr = generate_randomness(size);
    vector<F> x = generate_randomness((int)log2(size));    
    
    vector<__hhash_digest> leaves;
    __hhash_digest comm;
    
    printf("Committing\n");
    vector<vector<F>> encoded_poly = FFT_breakdown_commit(arr,comm,leaves);
    printf("proving time : %lf \n",proving_time);
    clock_t t1,t2;
    t1 = clock();
    poly_proof P = FFT_breakdown_open(arr, encoded_poly, x);
    t2 = clock();
    printf("Open time : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    printf("%d,%d\n",P.challenge_vector.size(),P.collumns.size(),P.collumns[0].size());
    printf("Proof size: %lf MB\n",(8.0*(P.challenge_vector.size() + P.tensor.size() + P.collumns.size()*P.collumns[0].size()))/(1024.0*1024.0));
    /*
    t1 = clock();
    naive_breakdown_verify(P,x);
    t2 = clock();
    printf("Verification time : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
*/
}



vector<double> pigeon_brakedown_verify(poly_proof P){
    int size = 0;
    for(int i = 0; i < P.paths.size(); i++){
        size += P.paths[i].path.size()*8;
    }
    size += P.query_points.size()*P.query_points[0].size()*32;
    for(int i = 0; i < P.P_open.Fri.Proofs.size(); i++){
        size += 64*(P.P_open.Fri.Proofs[i].path.size() +1);
    }
    for(int i = 0; i < P.P_open.query_paths.size(); i++){
        size += 64*(P.P_open.query_paths[i].path.size()+1);
    }
    if(P.P_open.query_points.size()> 0){
        size += 16*P.P_open.query_points.size()*P.P_open.query_points[0].size();
    }
    size += 8*P.collumns.size()*P.collumns[0].size();
    printf("Proof size : %lf MB\n", (double)(size)/(1024.0*1024.0));
    
    clock_t s1,s2;
    s1 = clock();
    vector<__hhash_digest> buff(QUERIES_LE);
    for(int i = 0; i < buff.size(); i++){
        memset(&buff[i], 0, sizeof(__hhash_digest));
    }

    for(int i = 0; i < QUERIES_LE; i++){
        for(int j = 0; j < P.collumns.size()/4; j++){
            buff[i] = merkle_tree::hash_double_field_element_merkle_damgard(P.collumns[4*j][i], P.collumns[4*j+1][i],P.collumns[4*j+2][i],P.collumns[4*j+3][i], buff[i]);
        }
    }
    
    for(int i = 0; i < P.P_open.query_paths.size(); i++){
        MT_verify(P.P_open.query_paths[i],P.P_open.query_points[i],P.P_open.query_paths[i].idx);
    }
    
    printf("%d,%d\n",P.paths.size(),P.query_points.size());
    for(int i = 0; i < P.paths.size(); i++){
        MT_verify(P.paths[i],P.query_points[i],P.paths[i].idx);
    }
    for(int i = 0; i < P.P_open.Fri.Proofs.size(); i++){
        MT_verify(P.P_open.Fri.Proofs[i],P.P_open.Fri.query_points[i],P.P_open.Fri.Proofs[i].idx);
    }
    s2 = clock();
    printf("Verification time : %lf\n",2.0*(double)(s2-s1)/(double)CLOCKS_PER_SEC);
    vector<double> data;data.push_back(2.0*(double)(s2-s1)/(double)CLOCKS_PER_SEC);data.push_back((double)(size)/(1024.0*1024.0));
    return data;
}

void test_pigeon(size_t size, int r_size){
    vector<F> arr = generate_randomness(size);
    row_size = r_size;
    __hhash_digest C;
    vector<vector<__hhash_digest>> MT_hashes;
    clock_t s,e; 
    proving_time = 0.0;
    vector<vector<F>> encoded_matrix = Pigeon_breakdown_commit(arr , C, MT_hashes);
    
    printf("Commit time : %lf\n",proving_time);
    
    s =  clock();
    poly_proof P = Pigeon_breakdown_open(arr , encoded_matrix, generate_randomness((int)log2(arr.size())));
    e = clock();
    printf("Open time : %lf, total : %lf\n",(double)(e-s)/(double)CLOCKS_PER_SEC,(double)(e-s)/(double)CLOCKS_PER_SEC + proving_time);
    pigeon_brakedown_verify(P);

}
void test_pigeon_stream(int size, int r_size){
    row_size = r_size;
    stream_descriptor fd;fd.name = "test";fd.size = size;
    __hhash_digest C;
    vector<vector<__hhash_digest>> MT_hashes;
    clock_t s,e; 
    
    s =  clock();
    Pigeon_breakdown_commit_stream(fd , C, MT_hashes);
    e = clock();
    
    printf("Commit time : %lf\n",(double)(e-s)/(double)CLOCKS_PER_SEC);
    s =  clock();
    poly_proof P = Pigeon_breakdown_open_stream(fd , generate_randomness((int)log2(fd.size)));
    e = clock();
    printf("Open time : %lf\n",(double)(e-s)/(double)CLOCKS_PER_SEC);
    pigeon_brakedown_verify(P);
}

