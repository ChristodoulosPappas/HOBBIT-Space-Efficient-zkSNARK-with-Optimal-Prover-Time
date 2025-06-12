
#include "sumcheck.h"
#include "virgo_PC.h"
#include "Our_PC.hpp"
#include "GKR_standard.h"
#include "prove_encodings.h"
#include "Virgo.h"
#include "PC_utils.h"

using namespace std;
// For RS codes : 240, for linear codes : 1900
extern int aggregation_queries; 
PC_data graph_PC_data;
vector<vector<vector<F>>> graph_commitment;

// If 1 then use RS in both coding schemes
// Otherwhise first use RS for rows and then Spielman for collumns
extern int tensor_code;

extern double Elastic_PC_vt,Elastic_PC_ps,Elastic_PC_pt;
bool linear_time = false;
extern double sc_vt;
vector<vector<vector<F>>> tensor;
extern __hhash_digest virgo_Commitment;
extern shockwave_data *C_f;
extern shockwave_data *C_c;

void _compute_tensorcode_linear_code(vector<F> &message, vector<vector<F>> &tensor){
    if(tensor.size() == 0){
        tensor.resize(2*tensor_row_size);
        for(int i = 0; i < 2*tensor_row_size; i++){
            tensor[i].resize(2*message.size()/tensor_row_size,F(0));
        }
    }else{
        for(int i = 0; i < tensor.size(); i++){
            for(int j = 0; j < tensor[i].size(); j++){
                tensor[i][j] = F(0);
            }
        }
    }
    vector<F> buff(tensor[0].size()/2);
    for(int i = 0; i < tensor.size()/2; i++){
        for(int j = 0; j < buff.size(); j++){
            buff[j] = message[i*buff.size() + j];
        }
        encode_monolithic(buff.data(),tensor[i].data(),buff.size());
    }
    
    vector<F> buff2(tensor.size());
    buff.clear();
    buff.resize(tensor.size()/2,F(0));
    for(int i = 0; i < tensor[0].size(); i++){
        for(int j = 0; j < buff.size(); j++){
            buff[j] = tensor[j][i];
        }
        encode_monolithic(buff.data(),buff2.data(),buff.size());
        for(int j = 0; j < buff2.size(); j++){
            tensor[j][i] = buff2[j];
            buff2[j] = 0;

        }
    }
    printf("OK\n");
  
}

void _update_reply(vector<F> &message, vector<vector<F>> &tensor, vector<vector<size_t>> I,int idx,vector<vector<F>> &reply){
    if(tensor.size() == 0){
        tensor.resize(2*tensor_row_size);
        for(int i = 0; i < 2*tensor_row_size; i++){
            tensor[i].resize(2*message.size()/tensor_row_size,F(0));
        }
    }else{
        for(int i = 0; i < tensor.size(); i++){
            for(int j = 0; j < tensor[i].size(); j++){
                tensor[i][j] = F(0);
            }
        }
    }
    for(int i = 0; i < tensor_row_size; i++){
        for(int j = 0; j < message.size()/tensor_row_size; j++){
            tensor[i][j] = message[i*message.size()/tensor_row_size + j];
        }
    }
    
   
    #pragma omp parallel for
    for(int i = 0; i < tensor_row_size; i++){        
        _fft(tensor[i].data(),((int)log2(message.size()/tensor_row_size))+1,false);
    }


   
    #pragma omp parallel for
    for(int i = 0; i < I.size(); i++){
        vector<F> buff(2*tensor_row_size,F(0));
        for(int j = 0; j < tensor_row_size; j++){
            buff[j] = tensor[j][I[i][0]];
        }
        if(tensor_code == 1){
            _fft(buff.data(),(int)log2(2*tensor_row_size),false);
        }else{
            vector<F> buff2(2*tensor_row_size);
            encode(buff.data(),buff2.data(),buff.size());
        }
        reply[i][idx] = buff[I[i][1]];
        //for(int j = 0; j < 2*tensor_row_size; j++){
        //    tensor[j][i] = buff[j];
        //}
    }
    
}

void commit_brakingbase(vector<F> &poly, vector<vector<_hash>> &MT_hashes){
    tensor.resize(1);
    BUFFER_SPACE = tensor_row_size;
    vector<F> buffer(BUFFER_SPACE);
    tensor[0].resize(poly.size()/BUFFER_SPACE);
    printf("%d,%d\n",BUFFER_SPACE,tensor[0].size());
    for(int i = 0; i < tensor[0].size(); i++){
        tensor[0][i].resize(2*BUFFER_SPACE,F(0));
        for(int j = 0; j < BUFFER_SPACE; j++){
            buffer[j] = poly[i*BUFFER_SPACE+j];
        }
        encode_monolithic(buffer.data(),tensor[0][i].data(),buffer.size());
    }
    int counter= 0;
    vector<F> buff(tensor[0].size());
    vector<_hash> leaf(tensor[0][0].size());
    vector<vector<_hash>> H;
    for(int i = 0; i < leaf.size(); i++){
        for(int j = 0; j < buff.size(); j++){
            buff[j] = tensor[0][j][i];
        }
        merkle_tree::merkle_tree_prover::MT_commit_Blake(buff.data(),H,buff.size());
        leaf[i] = H[H.size()-1][0];
        H.clear();

    }
    MT_hashes.resize((int)log2(leaf.size())+1);
    MT_hashes[0] = leaf;
    //_compute_tensorcode_linear_code(poly,tensor[0]);
    merkle_tree::merkle_tree_prover::create_tree_blake(leaf.size(),MT_hashes,sizeof(__hhash_digest), true);
}

void commit_standard(vector<F> &poly, _hash &comm, vector<vector<_hash>> &MT_hashes, vector<vector<vector<F>>> &_tensor, int K){
    int BUFFER_SPACE = poly.size()/K; 
    vector<F> buff(BUFFER_SPACE);
    _tensor.resize(K);
    vector<_hash> buff_hash(BUFFER_SPACE);
    int counter= 0;
    MT_hashes.resize((int)log2(BUFFER_SPACE)+1);
    MT_hashes[0].resize(BUFFER_SPACE);// = buff_hash;
    
    for(int i = 0; i < K; i++){
        for(int j = 0; j < BUFFER_SPACE; j++){
            buff[j] = poly[i*BUFFER_SPACE +j];
        }
        compute_tensorcode(buff,_tensor[i]);
        
        #pragma omp parallel for
        for(int j = 0; j < tensor_row_size/2; j++){
            for(int k = 0; k < _tensor[i][0].size(); k++){
                MT_hashes[0][j*_tensor[i][0].size()+k] = merkle_tree::hash_double_field_element_merkle_damgard_blake(_tensor[i][4*j][k],_tensor[i][4*j+1][k],_tensor[i][4*j+2][k],_tensor[i][4*j+3][k], MT_hashes[0][j*_tensor[i][0].size()+k]);
            }
        }
    }
    
    merkle_tree::merkle_tree_prover::create_tree_blake( buff.size() , MT_hashes, sizeof(__hhash_digest), true);
    
}

void commit_standard_orion(vector<F> &poly, _hash &comm, vector<vector<_hash>> &MT_hashes){
    int n = (int)log2(poly.size());
    int BUFFER_SPACE;
    if(n%2 == 0){
        BUFFER_SPACE = 1ULL<<(n/2);
        expander_init_store(BUFFER_SPACE);
    }else{
        BUFFER_SPACE = 1ULL<<((n-1)/2);
        expander_init_store(2*BUFFER_SPACE);
    }
    
    tensor.resize(1);
    tensor[0].resize(2*poly.size()/BUFFER_SPACE);
    for(int i = 0; i < tensor[0].size(); i++){
        tensor[0][i].resize(2*BUFFER_SPACE,F(0));
    }
    int counter= 0;
    
    _compute_tensorcode_linear_code(poly,tensor[0]);
    vector<F> v = convert2vector(tensor[0]);
    merkle_tree::merkle_tree_prover::MT_commit_Blake(v.data(),MT_hashes,v.size());

}

void commit_standard_brakedown(vector<F> &poly, _hash &comm, vector<vector<_hash>> &MT_hashes){
    int n = (int)log2(poly.size());
    int BUFFER_SPACE;
    if(n%2 == 0){
        BUFFER_SPACE = 1ULL<<(n/2 + 6);
        expander_init_store(BUFFER_SPACE);
    }else{
        BUFFER_SPACE = 1ULL<<((n-1)/2 + 6);
        expander_init_store(BUFFER_SPACE);
    }
    
    tensor.resize(1);
    vector<F> buffer(BUFFER_SPACE);
    tensor[0].resize(poly.size()/BUFFER_SPACE);
    for(int i = 0; i < tensor[0].size(); i++){
        tensor[0][i].resize(2*BUFFER_SPACE,F(0));
        for(int j = 0; j < BUFFER_SPACE; j++){
            buffer[j] = poly[i*BUFFER_SPACE+j];
        }
        encode_monolithic(buffer.data(),tensor[0][i].data(),buffer.size());
    }
    int counter= 0;
    vector<F> buff(tensor[0].size());
    vector<_hash> leaf(tensor[0][0].size());
    vector<vector<_hash>> H;
    for(int i = 0; i < leaf.size(); i++){
        for(int j = 0; j < buff.size(); j++){
            buff[j] = tensor[0][j][i];
        }
        merkle_tree::merkle_tree_prover::MT_commit_Blake(buff.data(),H,buff.size());
        leaf[i] = H[H.size()-1][0];
        H.clear();

    }
    MT_hashes.resize((int)log2(leaf.size())+1);
    MT_hashes[0] = leaf;
    //_compute_tensorcode_linear_code(poly,tensor[0]);
    merkle_tree::merkle_tree_prover::create_tree_blake(leaf.size(),MT_hashes,sizeof(__hhash_digest), true);

}

void _aggregate_brakingbase(vector<F> &poly, vector<F> beta1,vector<F> random_points, vector<F> &codeword){
    int BUFFER_SPACE = tensor_row_size;
    
    vector<F> aggregated_vector(BUFFER_SPACE);
    int counter = 0;
    codeword.resize(2*BUFFER_SPACE);
    for(int i = 0; i < poly.size()/BUFFER_SPACE; i++){
        
        #pragma omp parallel for
        for(int j = 0; j < BUFFER_SPACE; j++){
            aggregated_vector[j] += beta1[i]*poly[i*BUFFER_SPACE+j];
        }
    }

    encode_monolithic(aggregated_vector.data(),codeword.data(),aggregated_vector.size());
        
    //buff.insert(buff.begin(),aggregated_vector.begin(),aggregated_vector.end());
    C_c = shockwave_commit(codeword,32);
}

void _aggregate(vector<F> &poly, vector<F> beta1,vector<F> random_points, vector<F> &aggregated_vector, vector<vector<F>> &aggregated_tensor, bool linear_time, int K){
    int BUFFER_SPACE = poly.size()/K;
    if(aggregated_vector.size() == 0){
        aggregated_vector.resize(BUFFER_SPACE,F(0));
    }
    
    int counter = 0;

    for(int i = 0; i < poly.size()/BUFFER_SPACE; i++){
        
        #pragma omp parallel for
        for(int j = 0; j < BUFFER_SPACE; j++){
            aggregated_vector[j] += beta1[i]*poly[i*BUFFER_SPACE+j];
        }
    }
    
    vector<F> buff = aggregated_vector;
    C_f = shockwave_commit(buff,32);
    
    if(linear_time){
        compute_tensorcode(aggregated_vector,aggregated_tensor);
        
        int rows = aggregated_tensor.size();
        for(int i = 0; i < rows/2; i++){
            aggregated_tensor.erase(aggregated_tensor.begin());
        }
        buff = convert2vector(aggregated_tensor);
        //buff.insert(buff.begin(),aggregated_vector.begin(),aggregated_vector.end());
        C_c = shockwave_commit(buff,32);
    }
    
}

void _compute_aggregation_reply(vector<vector<size_t>> &I, vector<vector<F>> &reply, vector<vector<vector<F>>> &_tensor, int K){
    
    //vector<F> buff(BUFFER_SPACE);
    reply.resize(aggregation_queries);
    for(int i = 0; i < reply.size(); i++){
        reply[i].resize(K);
    }
   
    for(int i = 0; i < K; i++){
        for(int k = 0; k < I.size(); k++){
            reply[k][i] = _tensor[i][I[k][1]][I[k][0]];
        }
    }
    
}



void _recursive_prover_orion(vector<F> &beta,vector<F> &v_r, vector<size_t> &I, vector<size_t> &J){
    vector<size_t> I_sorted,C;
    clock_t t1,t2;
    t1 = clock();
    I_sorted = I;
    int query_points = 3900;

    std::sort(I_sorted.begin(), I_sorted.end());//, _compareFirstElement);
    C.push_back(I_sorted[0]);
    for(int i = 1; i < I_sorted.size(); i++){
        if(I_sorted[i] != I_sorted[i-1]){
            C.push_back(I_sorted[i]);
        }
    }
    vector<F> aggr_beta(tensor[0][0].size()/2,F(0)),aggr_r(tensor[0][0].size()/2,F(0));
    for(int i = 0; i < tensor[0].size()/2; i++){
        for(int j = 0; j < tensor[0][i].size()/2; j++){
            aggr_beta[j] += tensor[0][i][j]*beta[i];
            aggr_r[j] += tensor[0][i][j]*v_r[i];
        }
    }
    vector<vector<F>> collumns(I.size());
    for(int i = 0; i < I.size(); i++){
        collumns[i].resize(tensor[0].size()/2);
        for(int j = 0; j < collumns[i].size(); j++){
            collumns[i][j] = tensor[0][j][I[i]];
        }
    }
    printf("%d,%d\n",collumns.size(),collumns[0].size());
    if(collumns[0].size() != aggr_beta.size()){
        aggr_beta.resize(collumns[0].size(),F(0));
        aggr_r.resize(collumns[0].size(),F(0));
    }
    J.resize(query_points);
    for(int i = 0; i < J.size(); i++){
        J[i] = rand()%(tensor.size());
    }
    collumns.push_back(aggr_beta);
    collumns.push_back(aggr_r);
    t2 = clock();

    prove_encodings_orion(collumns,J);
    Elastic_PC_pt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    
}

void open_brakingbase(vector<F> &poly,vector<F> x,vector<vector<_hash>> &MT_hashes){
    BUFFER_SPACE = tensor_row_size;
    Elastic_PC_vt = 0.0;
    Elastic_PC_ps = 0.0;
    double vt = 0.0,ps =0.0;
    int queries = 2935;
    
    vector<F> x1,x2;
    vector<F> r_v;
    vector<vector<F>> aggr_tensor;
    vector<F> codeword;
    aggregation_queries = queries;
    
    for(int i = 0; i < (int)log2(poly.size()/BUFFER_SPACE); i++){x1.push_back(x[i]);}
    for(int i = (int)log2(poly.size()/BUFFER_SPACE); i < x.size(); i++){x2.push_back(x[i]);}
    vector<F> beta;

    precompute_beta(x1,beta);
    r_v.resize(beta.size());
    r_v[0] = generate_randomness(1)[0];
    for(int i = 1; i < r_v.size(); i++){
        r_v[i] = r_v[i-1]*r_v[0];
    }
    

    _aggregate_brakingbase(poly ,beta,r_v,codeword);
    
    vector<size_t> I(queries);
    for(int i  = 0; i < I.size(); i++){
        I[i] = rand()%(tensor[0][0].size());
    }
    vector<vector<F>> reply(queries);
    for(int i = 0; i < reply.size(); i++){
        reply[i].resize(tensor[0].size());
        for(int j = 0; j < tensor[0].size(); j++){
            reply[i][j] = tensor[0][j][I[i]];
        }
    }
    ps += (double)(reply[0].size()*reply.size()*sizeof(F))/(1024.0); 
    vector<vector<_hash>> commitment_paths;
    vector<size_t> c(2);
    for(int i = 0; i < I.size(); i++){
        c[0] = 0;c[1] = I[i];
        commitment_paths.push_back(merkle_tree::merkle_tree_prover::open_tree_blake(MT_hashes,c,0));
    }
    
    recursive_prover_brakingbase(codeword, I, vt, ps);

    clock_t t1 = clock();
    vector<vector<_hash>> hashes;
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_prover::MT_commit_Blake(reply[i].data(),hashes,reply[i].size());
        hashes.clear();
    }
    
    for(int i = 0; i < I.size(); i++){
        F sum1 = F(0),sum2 = F(0);
        for(int j = 0; j < reply.size(); j++){
            //sum1 += r[j]*reply[i][j];
            sum2 += beta[j]*reply[i][j];
        }
    }
    bool *visited = new bool[2*MT_hashes[0].size()];
    for(int i = 0; i <2*MT_hashes[0].size(); i++){
        visited[i] = false;
    }
    
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(MT_hashes,commitment_paths[i].data(),I[i],MT_hashes[0].size(),visited,ps);    
    }
    
    clock_t t2 = clock();
    vt+= (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    printf("Ps : %lf, Vt : %lf \n",ps,vt);
}


void open_brakedown_standard(vector<F> &poly , vector<F> x,  vector<vector<_hash>> &Commitment_MT){
    Elastic_PC_vt = 0.0;
    Elastic_PC_ps = 0.0;
    Elastic_PC_pt = 0.0;
    clock_t t1,t2;
    t1 = clock();
    
    int n = (int)log2(poly.size());
    int BUFFER_SPACE;
    if(n%2 == 0){
        BUFFER_SPACE = 1ULL<<(n/2+ 6);
    }else{
        BUFFER_SPACE = 1ULL<<((n-1)/2+ 6);
    }
    vector<F> beta1,r;
    vector<F> r1;
    for(int i = 0; i < (int)log2(tensor[0].size()); i++){
        r1.push_back(x[i]);
        
    }
    precompute_beta(r1,beta1);
    for(int i = 0; i < beta1.size(); i++){
        r.push_back(random());
    }
    vector<F> aggr_beta(tensor[0][0].size()/2,F(0)),aggr_r(tensor[0][0].size()/2,F(0));
    for(int i = 0; i < tensor[0].size(); i++){
        for(int j = 0; j < tensor[0][i].size()/2; j++){
            aggr_beta[j] += beta1[i]*tensor[0][i][j];
            aggr_r[j] += r[i]*tensor[0][i][j];
        }
    }
    vector<size_t> I(2900);
    for(int i  = 0; i < I.size(); i++){
        I[i] = rand()%(tensor[0][0].size());
    }
    vector<vector<F>> reply(2900);
    for(int i = 0; i < reply.size(); i++){
        reply[i].resize(tensor[0].size());
        for(int j = 0; j < tensor[0].size(); j++){
            reply[i][j] = tensor[0][j][I[i]];
        }
    }
    
    vector<vector<_hash>> commitment_paths;
    vector<size_t> c(2);
    for(int i = 0; i < I.size(); i++){
        c[0] = 0;c[1] = I[i];
        commitment_paths.push_back(merkle_tree::merkle_tree_prover::open_tree_blake(Commitment_MT,c,0));
    }
    
    
    t2 = clock();
    Elastic_PC_pt = (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    // Verifier:

    t1 = clock();
    vector<vector<_hash>> hashes;
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_prover::MT_commit_Blake(reply[i].data(),hashes,reply[i].size());
        hashes.clear();
    }
    vector<F> code_beta(2*BUFFER_SPACE),code_r(2*BUFFER_SPACE);
    encode_monolithic(aggr_beta.data(),code_beta.data(),aggr_beta.size());
    encode_monolithic(aggr_r.data(),code_r.data(),aggr_r.size());
    for(int i = 0; i < I.size(); i++){
        F sum1 = F(0),sum2 = F(0);
        for(int j = 0; j < reply.size(); j++){
            sum1 += r[j]*reply[i][j];
            sum2 += beta1[j]*reply[i][j];
        }
    }
    bool *visited = new bool[2*Commitment_MT[0].size()];
    for(int i = 0; i <2*Commitment_MT[0].size(); i++){
        visited[i] = false;
    }
    
    double ps;
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(Commitment_MT,commitment_paths[i].data(),I[i],Commitment_MT[0].size(),visited,ps);    
    }
    
    t2 = clock();
    Elastic_PC_vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    ps += (double)(reply.size()*reply[0].size()*sizeof(F))/1024.0;
    ps += (2*aggr_beta.size()*sizeof(F))/1024.0;
    Elastic_PC_ps += ps;
    printf("PC Open: pt = %lf, ps = %lf KB, vt = %lf sec\n",Elastic_PC_pt, Elastic_PC_ps,Elastic_PC_vt);
    
}


void open_orion_standard(vector<F> &poly , vector<F> x,  vector<vector<_hash>> &Commitment_MT){
    BUFFER_SPACE = 1ULL<<((int)log2(poly.size())/2);
    Elastic_PC_vt = 0.0;
    Elastic_PC_ps = 0.0;
    Elastic_PC_pt = 0.0;
    vector<vector<_hash>> Aggregated_MT;
    vector<F> x1,x2;
    vector<F> r_v;
    vector<F> aggr_vector;
    double vt = 0.0,ps = 0.0;
    
    for(int i = 0; i < (int)log2(poly.size()/BUFFER_SPACE); i++){x1.push_back(x[i]);}
    for(int i = (int)log2(poly.size()/BUFFER_SPACE); i < x.size(); i++){x2.push_back(x[i]);}
    vector<F> beta;

    precompute_beta(x1,beta);
    r_v.resize(beta.size());
    r_v[0] = generate_randomness(1)[0];
    for(int i = 1; i < r_v.size(); i++){
        r_v[i] = r_v[i-1]*r_v[0];
    }
    
    
    
    vector<size_t> I,J;
    if(BUFFER_SPACE >= 1ULL<<12){
        for(int i = 0; i < 1ULL<<12; i++){
            I.push_back(rand()%(2*BUFFER_SPACE));
            J.push_back(rand()%(2*BUFFER_SPACE));
        }
    }else{
        for(int i = 0; i < BUFFER_SPACE; i++){
            I.push_back(rand()%(2*BUFFER_SPACE));
            J.push_back(rand()%(2*BUFFER_SPACE));
        }
    }
    
    vector<vector<F>> s_columns(I.size()),codewords(I.size());
    for(int i = 0; i < s_columns.size(); i++){
        s_columns[i].resize(BUFFER_SPACE);
        codewords[i].resize(2*BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            s_columns[i][j] = tensor[0][j][I[i]];
        }
        encode_monolithic(s_columns[i].data(),codewords[i].data(),s_columns[i].size());
    }
    
    recursive_prover_orion(codewords, vt,ps);
    ps += (1ULL<<20)*sizeof(F)/1024.0;
    vector<size_t> pos(2);
    vector<vector<_hash>> commitment_paths;
    for(int i = 0; i < I.size(); i++){
        for(int j = 0; j < J.size(); j++){
            pos[0] = I[i];
            pos[1] = J[j];
            commitment_paths.push_back(merkle_tree::merkle_tree_prover::open_tree_blake(Commitment_MT,pos,2*BUFFER_SPACE));
        }
    }
    
    //printf("Merkle Proofs : %lf \n", (double)((commitment_paths.size()*commitment_paths[0].size())*32)/1024.0);
    //Elastic_PC_ps += (double)((commitment_paths.size()*commitment_paths[0].size())*32)/1024.0;
    
    bool *visited = new bool[2*Commitment_MT[0].size()];
    clock_t t1,t2;
    t1 = clock();
    for(int i = 0; i < I.size(); i++){
        for(int j = 0; j < J.size(); j++){
            pos[0] = I[i]/2;
            pos[1] = J[j]/2;
            ps += 2*sizeof(F)/1024.0;
            merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(Commitment_MT,commitment_paths[i].data(),(pos[1])*BUFFER_SPACE+pos[0],Commitment_MT[0].size(),visited,ps);    
      }
    }
    
    t2 = clock();
    vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    printf(" ps = %lf, vt = %lf\n", ps,vt);
    

}

void open_standard(vector<F> &poly , vector<F> x,  vector<vector<_hash>> &Commitment_MT,vector<vector<vector<F>>> &_tensor ,int K, double &vt,double &ps){
    BUFFER_SPACE = poly.size()/K;
    Elastic_PC_vt = 0.0;
    Elastic_PC_ps = 0.0;
    //double vt = 0.0,ps =0.0;
    int queries = 5900;
    if(!linear_time){
        queries = 790;
    }
    vector<F> x1,x2;
    vector<F> r_v;
    vector<vector<F>> aggr_tensor;
    vector<F> aggr_vector;
    aggregation_queries = queries;
    
    for(int i = 0; i < (int)log2(poly.size()/BUFFER_SPACE); i++){x1.push_back(x[i]);}
    for(int i = (int)log2(poly.size()/BUFFER_SPACE); i < x.size(); i++){x2.push_back(x[i]);}
    vector<F> beta;

    precompute_beta(x1,beta);
    r_v.resize(beta.size());
    r_v[0] = generate_randomness(1)[0];
    for(int i = 1; i < r_v.size(); i++){
        r_v[i] = r_v[i-1]*r_v[0];
    }
    
    _aggregate(poly ,beta,r_v,aggr_vector,aggr_tensor,linear_time,K);
    
    
    vector<vector<size_t>> I(queries);
    vector<size_t> I_v(queries);
    for(int i = 0; i < queries; i++){
        I[i].push_back(rand()%(2*BUFFER_SPACE/tensor_row_size));
        I[i].push_back(rand()%(2*tensor_row_size));
        I_v[i] = I[i][0] + (2*BUFFER_SPACE/tensor_row_size)*I[i][1];
    }
    vector<vector<F>> reply;
    _compute_aggregation_reply(I,reply,_tensor,K);
    vector<vector<_hash>> commitment_paths;
    vector<vector<_hash>> aggregated_commitment_paths;
    printf(">>OK\n");
    for(int i = 0; i < I.size(); i++){
        commitment_paths.push_back(merkle_tree::merkle_tree_prover::open_tree_blake(Commitment_MT,I[i],2*BUFFER_SPACE/tensor_row_size));
    }
    
    //printf("Aggregation size : %lf KB\n",(double)(reply.size()*reply[0].size()*sizeof(virgo::fieldElement))/1024.0);
    //printf("Merkle Proofs : %lf \n", (double)((commitment_paths.size()*commitment_paths[0].size())*32)/1024.0);
    ps += (double)(reply.size()*reply[0].size()*sizeof(virgo::fieldElement))/1024.0;
    printf(">> %lf Kb\n",(double)(reply.size()*reply[0].size()*sizeof(virgo::fieldElement))/1024.0);
    if(!linear_time){
        recursive_prover_RS(aggr_vector, I,vt,ps );
    }else{
        recursive_prover_Spielman(aggr_vector,aggr_tensor,I_v,vt,ps );
    }
    
    bool *visited = new bool[Commitment_MT[0].size()*2];
    for(int i = 0; i < Commitment_MT[0].size()*2; i++){
        visited[i] = false;
    }
    clock_t t1,t2;
    double MT_ps = 0.0;
    t1 = clock();
    vector<vector<_hash>> H;
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_prover::MT_commit_Blake(reply[i].data(),H,reply[i].size());
        H.clear();
    }
    F s = 0;
    for(int i = 0; i < I.size(); i++){
        for(int j = 0; j < reply[i].size(); j++){
            s += beta[j]*reply[i][j];
        }
    }
    for(int i = 0; i < commitment_paths.size(); i++){
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(Commitment_MT,commitment_paths[i].data(),(I[i][1]/4)*2*BUFFER_SPACE/tensor_row_size+I[i][0],Commitment_MT[0].size(),visited,MT_ps);
    }
    t2 = clock();
    printf("Opening proofs : %lf\n",MT_ps);
    //printf("%lf\n",ps);
    ps += MT_ps;
    //Elastic_PC_ps += MT_ps;
    //Elastic_PC_ps += ps;
    vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    //vt += Elastic_PC_vt;
    //printf("PC : ps = %lf, vt = %lf\n",Elastic_PC_ps,Elastic_PC_vt);
    // Virgo Open 


}

void test_tensorcodes(size_t N, int option){
    vector<F> poly = generate_randomness(N);
    F num = F(3234);
    poly[0] = num;
    for(int i = 1; i < poly.size(); i++){
        poly[i] = poly[i-1]*num;
    }
    if(option == 1){
        linear_time = false;
        
        tensor_row_size = N/(1ULL<<(11));
        F** tensor = new F*[2*tensor_row_size];
        for(int i = 0; i < 2*tensor_row_size; i++){
            tensor[i] = new F[2*N/tensor_row_size];
        }
        //vector<vector<F>> tensor;
        auto start = std::chrono::steady_clock::now();
        for(int i = 0; i < 16; i++){
            _compute_tensorcode(poly.data() ,tensor, poly.size());
        }
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Encode time: " << commit_time << " seconds" << std::endl;
        
    }else if(option == 2){
        linear_time = true;
        tensor_row_size = N/(1ULL<<(10));
        vector<vector<F>> tensor;
        
        printf("%d\n",tensor_row_size);
        expander_init_store(tensor_row_size);
        auto start = std::chrono::steady_clock::now();
        compute_tensorcode(poly ,tensor);
        

        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Encode time: " << commit_time << " seconds" << std::endl;
    }else if(option == 3){
        poly.resize(2*poly.size(),F(0));  
        auto start = std::chrono::steady_clock::now();
        _fft(poly.data(),(int)log2(poly.size()),false);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Encode time: " << commit_time << " seconds" << std::endl;
    }else{
        expander_init_store(N);
        vector<F> buff(2*N,F(0));
        auto start = std::chrono::steady_clock::now();
        encode_monolithic(poly.data(),buff.data(),poly.size());
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Encode time: " << commit_time << " seconds" << std::endl;
    
    }

}


void test_PC(size_t N, int option, int K){
    vector<F> poly = generate_randomness(N);
    vector<vector<_hash>> hashes;
    _hash comm;
    vector<vector<_hash>> MT_hashes;
        
    if(option == 1){
        double vt = 0.0,ps = 0.0;
        tensor_row_size = 128;
        vector<vector<vector<F>>> _tensor;
        auto start = std::chrono::steady_clock::now();
        commit_standard(poly ,comm, MT_hashes,_tensor, K);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        
        start = std::chrono::steady_clock::now();
        open_standard(poly, generate_randomness((int)log2(poly.size())), MT_hashes,_tensor, K,vt,ps);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
    }
    else if(option == 2){
        
        auto start = std::chrono::steady_clock::now();
        commit_standard_orion(poly, comm, hashes);
        auto end = std::chrono::steady_clock::now();

        // Calculate the elapsed time in seconds
        double elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        start = std::chrono::steady_clock::now();
        std::cout << "Commit time: " << elapsed_seconds << " seconds" << std::endl;
        open_orion_standard(poly , generate_randomness(log2(N)),  hashes);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
    }else if(option == 3){
        auto start = std::chrono::steady_clock::now();
        commit_standard_brakedown(poly, comm, hashes);
        auto end = std::chrono::steady_clock::now();
        double elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Commit time: " << elapsed_seconds << " seconds" << std::endl;
        start = std::chrono::steady_clock::now();
        open_brakedown_standard(poly , generate_randomness(log2(N)),  hashes);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds  << " seconds" << std::endl;

    }else if(option == 4){
        double vt = 0.0,ps = 0.0;
        
        linear_time = true;
        tensor_row_size = N/(K*1ULL<<(11));
        
        printf("%d\n",tensor_row_size);
        expander_init_store(tensor_row_size);
        vector<vector<vector<F>>> _tensor;
        auto start = std::chrono::steady_clock::now();
        commit_standard(poly ,comm, MT_hashes,_tensor, K);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        start = std::chrono::steady_clock::now();
        open_standard(poly, generate_randomness((int)log2(poly.size())), MT_hashes,_tensor, K,vt,ps);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
        printf("%lf,%lf\n",ps,vt);  
    }else if(option == 5){
        tensor_row_size = N/(K);
        expander_init_store(tensor_row_size);
        auto start = std::chrono::steady_clock::now();
        commit_brakingbase(poly,MT_hashes);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        
        start = std::chrono::steady_clock::now();
        open_brakingbase(poly,generate_randomness((int)log2(poly.size())), MT_hashes);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
        
    }else{
        auto start = std::chrono::steady_clock::now();
        Whir_data C;
        whir_commit(poly,C);
        //virgo_Commitment = virgo_commit(poly);
        auto end = std::chrono::steady_clock::now();
        double elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Commit time: " << elapsed_seconds << " seconds" << std::endl;
        
        start = std::chrono::steady_clock::now();
        double ps = 0.0,vt = 0.0;
        _whir_prove(C,generate_randomness(log2(N)),vt,ps);
        //virgo_open(poly,,virgo_Commitment,vt,ps);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        printf("PC Total: pt = %lf, ps = %lf, vt = %lf\n",elapsed_seconds, ps,vt);
    
    }
}