#include "Elastic_PC.hpp"
#include "sumcheck.h"
#include "Virgo.h"
#include "PC_utils.h"
#include <unistd.h>


using namespace std;
// For RS codes : 240, for linear codes : 1900
int aggregation_queries = 1900; 
extern shockwave_data *C_f,*C_c;
// If 1 then use RS in both coding schemes
// Otherwhise first use RS for rows and then Spielman for collumns
int tensor_code = 1;
extern F *scratch[2][100];
extern bool __encode_initialized;
double Elastic_PC_vt = 0.0,Elastic_PC_ps= 0.0;
double Elastic_PC_pt = 0.0;
extern double sc_vt;
extern bool linear_time;
__hhash_digest virgo_Commitment;

void compute_tensorcode_linear_code(vector<F> &message, vector<vector<F>> &tensor){
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
    vector<F> buff(message.size()/tensor_row_size);
    for(int i = 0; i < tensor_row_size; i++){
        for(int j = 0; j < message.size()/tensor_row_size; j++){
            buff[j] = message[i*message.size()/tensor_row_size + j];
        }
        encode(buff.data(),tensor[i].data(),buff.size());
    }
    vector<F> buff2(2*tensor_row_size);
    buff.clear();
    buff.resize(tensor_row_size,F(0));
    for(int i = 0; i < tensor[0].size(); i++){
        for(int j = 0; j < tensor_row_size; j++){
            buff[j] = tensor[j][i];
        }
        encode(buff.data(),buff2.data(),buff.size());
        for(int j = 0; j < 2*tensor_row_size; j++){
            tensor[j][i] = buff2[j];
            buff2[j] = 0;

        }
    }  
}

void update_reply(vector<F> &message, vector<vector<F>> &tensor, vector<vector<size_t>> I,int idx,vector<vector<F>> &reply){
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
    if(!linear_time){
        #pragma omp parallel for
        for(int i = 0; i < tensor_row_size; i++){        
            _fft(tensor[i].data(),((int)log2(message.size()/tensor_row_size))+1,false);
        }


        #pragma omp parallel for
        for(int i = 0; i < I.size(); i++){
            vector<F> buff(tensor_row_size,F(0));
            for(int j = 0; j < tensor_row_size; j++){
                buff[j] = tensor[j][I[i][0]];
            }
            if(!linear_time){
                buff.resize(2*tensor_row_size,F(0));
                fft(buff,(int)log2(2*tensor_row_size),false);
            reply[i].push_back(buff[I[i][1]]);
            }else{
                vector<F> buff2(2*tensor_row_size);
                encode_monolithic(buff.data(),buff2.data(),buff.size());
            reply[i].push_back(buff2[I[i][1]]);
            }
            //for(int j = 0; j < 2*tensor_row_size; j++){
            //    tensor[j][i] = buff[j];
            //}
        }
    }else{
        compute_tensorcode(message,tensor);
        for(int i = 0; i < I.size(); i++){
            reply[i][idx] = tensor[I[i][1]][I[i][0]];
        }
    }
    
    
}
void commit_brakedown_stream(stream_descriptor fd , vector<vector<_hash>> &MT_hashes){
    if(fd.size/BUFFER_SPACE <= 4){
        printf("Decrease buffer size\n");
        exit(-1);
    }
    F *buff = new F[BUFFER_SPACE];
    F *codeword = new F[2*BUFFER_SPACE];
    F **commit_input = new F*[3];
    for(int i = 0; i < 3; i++){
        commit_input[i] = new F[2*BUFFER_SPACE];
    }
    _hash *buff_hash = new _hash[BUFFER_SPACE*2];
    virgo::fieldElement element[2];element[0] = 0;element[1] = 0;
    for(int i = 0; i < BUFFER_SPACE*2; i++){
        for(int j = 0; j < 32; j++){
            buff_hash[i].arr[j] = 0;
        }
        //memcpy(&buff_hash[i],element,2*sizeof(virgo::fieldElement));
    }
    double t = 0.0;
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        read_stream_PC(fd,buff,BUFFER_SPACE);
        clock_t t1,t2;
        t1 = clock();
        encode_monolithic(buff,codeword,BUFFER_SPACE);
        t2 = clock();
        t += (double)(t2-t1)/(double)(CLOCKS_PER_SEC);
        if(i%4 != 3){
            int counter = 0;
            for(int j = 0; j < 2*BUFFER_SPACE; j++){
                commit_input[i%4][counter++] = codeword[j];
            }
        }else{
            int counter = 0;
            for(int j = 0; j < 2*BUFFER_SPACE; j++){
                buff_hash[j] = merkle_tree::hash_double_field_element_merkle_damgard_blake(commit_input[0][counter],commit_input[1][counter]
                    ,commit_input[2][counter++],codeword[j], buff_hash[j]);
            }
            
        }
    }
    for(int i = 0 ; i < 3;i ++){
        delete[] commit_input[i];
    }
    delete[] commit_input;
    //printf("Encoding time: %lf\n",tensorcode_compute);
    delete[] buff;
    delete[] codeword;
    buff = 0;
    codeword = 0;
    
    //printf("%d\n",hash_num);
    
    MT_hashes.resize((int)log2(BUFFER_SPACE*2)+1);
    MT_hashes[0].resize(BUFFER_SPACE*2);
    for(int  i =0 ; i < MT_hashes[0].size(); i++){
        MT_hashes[0][i] = buff_hash[i];
    }
    delete[] buff_hash;
    merkle_tree::merkle_tree_prover::create_tree_blake( 2*BUFFER_SPACE , MT_hashes, sizeof(__hhash_digest), true);
    
}
void commit(stream_descriptor fd , _hash &comm, vector<vector<_hash>> &MT_hashes){
    if(fd.size/BUFFER_SPACE < 4){
        printf("Decrease buffer size %d\n",fd.size/BUFFER_SPACE);
        //exit(-1);
    }
    F *buff = new F[BUFFER_SPACE];
    F **commit_input = new F*[3];
    for(int i = 0; i < 3; i++){
        commit_input[i] = new F[4*BUFFER_SPACE];
    }
    F **tensor = new F*[2*tensor_row_size];
    for(int i = 0; i < 2*tensor_row_size; i++){
        tensor[i] = new F[2*BUFFER_SPACE/tensor_row_size];
    }
    double tensorcode_compute = 0.0;
    //vector<vector<F>> tensor;

    int counter= 0;

    _hash *buff_hash = new _hash[BUFFER_SPACE*4];
    virgo::fieldElement element[2];element[0] = 0;element[1] = 0;
    for(int i = 0; i < BUFFER_SPACE*4; i++){
        for(int j = 0; j < 32; j++){
            buff_hash[i].arr[j] = 0;
        }
        //memcpy(&buff_hash[i],element,2*sizeof(virgo::fieldElement));
    }
    int hash_num = 0;
    bool flag = false;
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        
        read_stream_PC(fd,buff,BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            if(buff[j] != F(0)){
                flag = true;
                break;
            }
        }
        //compute_tensorcode_linear_code(buff,tensor);
        if(flag){
            clock_t t1,t2;
            t1 = clock();
            _compute_tensorcode(buff,tensor,BUFFER_SPACE);
            t2 = clock();
            tensorcode_compute += (double)(t2-t1)/(double)CLOCKS_PER_SEC; 
       
        }else{
            for(int j = 0; j < 2*tensor_row_size; j++){
                for(int k = 0; k < 2*BUFFER_SPACE/tensor_row_size; k++){
                    tensor[j][k] = F(0);
                }
            }
        }
        
        if(i%4 != 3){
            int counter = 0;
            for(int j = 0; j < 2*tensor_row_size; j++){
                for(int k = 0; k < 2*BUFFER_SPACE/tensor_row_size; k++){
                    commit_input[i%4][counter++] = tensor[j][k];
                }
            }
        }else{
            int counter = 0;
            for(int j = 0; j < 2*tensor_row_size; j++){
                for(int k = 0; k < 2*BUFFER_SPACE/tensor_row_size; k++){
                    buff_hash[j* 2*BUFFER_SPACE/tensor_row_size+k] = merkle_tree::hash_double_field_element_merkle_damgard_blake(commit_input[0][counter],commit_input[1][counter]
                    ,commit_input[2][counter++],tensor[j][k], buff_hash[j* 2*BUFFER_SPACE/tensor_row_size+k]);
                }
            }
        }
        flag = false;
        /*
        #pragma omp parallel for
        for(int j = 0; j < 2*tensor_row_size; j++){
            __hhash_digest in[2];
            virgo::fieldElement el[2];el[1] = F(0);
            for(int k = 0; k < 2*BUFFER_SPACE/tensor_row_size; k++){
                in[0] = buff_hash[j*2*BUFFER_SPACE/tensor_row_size+k];
                el[0] = tensor[j][k];
                memcpy(&in[1],el,2* sizeof(virgo::fieldElement));
                my_hhash(in,&buff_hash[j*2*BUFFER_SPACE/tensor_row_size+k]);
                hash_num++;
            }
        }*/
        
    }
    
    for(int i = 0 ; i < 3;i ++){
        delete[] commit_input[i];
    }
    delete[] commit_input;
    //printf("Encoding time: %lf\n",tensorcode_compute);
    delete[] buff;
    buff = 0;
    for(int i = 0; i < 2*tensor_row_size; i++){
        delete[] tensor[i];
        tensor[i] = 0;
    }
    delete[] tensor;
    tensor = 0;
    
    //printf("%d\n",hash_num);
    
    MT_hashes.resize((int)log2(BUFFER_SPACE*4)+1);
    MT_hashes[0].resize(BUFFER_SPACE*4);
    for(int  i =0 ; i < MT_hashes[0].size(); i++){
        MT_hashes[0][i] = buff_hash[i];
    }
    delete[] buff_hash;
    merkle_tree::merkle_tree_prover::create_tree_blake( 4*BUFFER_SPACE , MT_hashes, sizeof(__hhash_digest), true);
    
}

void aggregate_brakedown(stream_descriptor fd , vector<F> beta1, vector<F> random_points, vector<F> &aggregated_vector1, vector<F> &aggregated_vector2){
    aggregated_vector1.resize(BUFFER_SPACE,F(0));
    aggregated_vector2.resize(BUFFER_SPACE,F(0));
    F *buff = new F[BUFFER_SPACE];
    for(int i  =0 ; i < fd.size/BUFFER_SPACE; i++){
        read_stream_PC(fd,buff,BUFFER_SPACE);
        for(int j = 0; j < BUFFER_SPACE; j++){
            aggregated_vector1[j] += beta1[i]*buff[j];
            aggregated_vector2[j] += random_points[i]*buff[j];
        }
    }
    delete[] buff;
}

void compute_reply(stream_descriptor fd, vector<size_t> I, vector<vector<F>> &R){
    F *buff = new F[BUFFER_SPACE];
    F *codeword = new F[2*BUFFER_SPACE];

    for(int i  =0 ; i < fd.size/BUFFER_SPACE; i++){
        read_stream_PC(fd,buff,BUFFER_SPACE);
        encode_monolithic(buff,codeword,BUFFER_SPACE);
        for(int j = 0; j < I.size(); j++){
            R[j].push_back(codeword[I[j]]);
        }
    }
    delete[] buff;
}
vector<vector<size_t>> I;
vector<vector<F>> aux_commit;
void aggregate(stream_descriptor fd , vector<F> beta1,vector<F> random_points, vector<vector<_hash>> &MT_hashes, vector<F> &aggregated_vector, vector<vector<F>> &aggregated_tensor){
    if(aggregated_vector.size() == 0){
        aggregated_vector.resize(BUFFER_SPACE,F(0));
    }
    //vector<F> aggregated_vector2(aggregated_vector.size(),F(0));
    vector<F> buff(BUFFER_SPACE);
    
    //vector<__hhash_digest> buff_hash(BUFFER_SPACE);
    int counter = 0;

    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        read_stream(fd,buff,buff.size());
        #pragma omp parallel for
        for(int j = 0; j < BUFFER_SPACE; j++){
            aggregated_vector[j] += beta1[i]*buff[j];
            //aggregated_vector2[j] += random_points[i]*buff[j];
        }
    }
    
    //buff.insert(buff.end(),aggregated_vector2.begin(),aggregated_vector2.end());
    /*
    F b = generate_randomness(1)[0];
    for(int i = 0; i < aggregated_vector.size(); i++){
        aggregated_vector[i] += b*aggregated_vector2[i];
    }
    */
    if(!linear_time){
        buff = aggregated_vector;
        C_f = shockwave_commit(buff,32);
    }
    else{
        clock_t t1,t2;
        C_f = shockwave_commit(aggregated_vector,32);
        
        
        std::unordered_map<size_t, vector<size_t>> column_map;
        vector<size_t> columns;

        for(int  i =0; i < I.size(); i++){
            columns.push_back(I[i][0]);
        }
        std::sort(columns.begin(), columns.end());
        auto it = std::unique(columns.begin(), columns.end());
        columns.erase(it, columns.end());
        for(int i = 0; i < I.size(); i++){
            column_map[I[i][0]].push_back(I[i][1]);
        }
        
        int counter = 0;
        aggregated_tensor.resize(tensor_row_size);
        for(int i = 0; i < tensor_row_size; i++){
            aggregated_tensor[i].resize(2*aggregated_vector.size()/tensor_row_size,F(0));
            if(i < tensor_row_size){
                for(int j = 0; j < aggregated_tensor[i].size()/2; j++){
                    aggregated_tensor[i][j] = aggregated_vector[counter++];
                }
                _fft(aggregated_tensor[i].data(),(int)log2(aggregated_tensor[i].size()),false);
            
            }
        }
        vector<int> remaining_columns;
        bool flag = false;
        for(int i = 0; i < columns.size(); i++){
            for(int j = 0; j < column_map[columns[i]].size(); j++){
                if(column_map[columns[i]][j] >= tensor_row_size){
                    flag = true;
                    break;
                }
            }
            if(flag){
                
                remaining_columns.push_back(columns[i]);
            }
            flag = false;
        }
       // printf("%d,%d,%d\n",remaining_columns.size(),columns.size(),remaining_columns.size()*tensor_row_size*2);
        
        t1 = clock();
        aux_commit.resize(remaining_columns.size());
        for(int i = 0; i < remaining_columns.size(); i++){
            vector<F> buff;
            
            for(int j = 0; j < aggregated_tensor.size(); j++){
                buff.push_back(aggregated_tensor[j][remaining_columns[i]]);
            }
            aux_commit[i].resize(2*buff.size());
            encode_monolithic(buff.data(),aux_commit[i].data(),buff.size());
        }

        
        t2 = clock();
        buff = convert2vector(aux_commit);
        printf("%d\n",buff.size());
        pad_vector(buff);
        t1 = clock();
        C_c = shockwave_commit(buff,32);
        t2 = clock();
        /*
        compute_tensorcode(aggregated_vector,aggregated_tensor);
        */
        //int rows = aggregated_tensor.size();
        //for(int i = 0; i < rows/2; i++){
        //    aggregated_tensor.erase(aggregated_tensor.begin());
        //}
        /*
        buff = convert2vector(aggregated_tensor);
        t1 = clock();
        C_c = shockwave_commit(buff,32);
        t2 = clock();
        printf(">> %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC); 
        */
               
    }
}

void update_reply_spielman(vector<F> &message, vector<vector<F>> &tensor, vector<vector<size_t>> I,int idx,vector<vector<F>> &reply,
            vector<size_t> &columns,std::unordered_map<size_t, vector<size_t>> &column_map){
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
    vector<F> buff(tensor_row_size);
    vector<F> buff2(2*tensor_row_size);
    int counter = 0;
    int m = 0;
    bool flag = false;
    for(int i = 0; i < columns.size(); i++){
      
        for(int j = 0; j < tensor_row_size; j++){
            buff[j] = tensor[j][columns[i]];
        }
        for(int j = 0; j < column_map[columns[i]].size(); j++){
            if(column_map[columns[i]][j] >= tensor_row_size){
                m++;
                flag = true;
                break;
            }
        }
        if(flag){
            buff2 = buff;
        }else{
            encode_monolithic(buff.data(),buff2.data(),buff.size());
        }
        
        for(int j = 0; j < column_map[columns[i]].size(); j++){
            reply[counter++].push_back(buff2[column_map[columns[i]][j]]);
        }
        flag = false;
        //printf("%d\n",counter);
    }
    //printf("%d,%d\n",m,columns.size());

}

void compute_aggregation_reply(stream_descriptor fd ,vector<vector<size_t>> &I, vector<vector<F>> &reply){
    std::unordered_map<size_t, vector<size_t>> column_map;
    vector<size_t> columns;
    vector<F> buff(BUFFER_SPACE);
    vector<vector<F>> tensor;

    for(int  i =0; i < I.size(); i++){
        columns.push_back(I[i][0]);
    }
    std::sort(columns.begin(), columns.end());
    auto it = std::unique(columns.begin(), columns.end());
    columns.erase(it, columns.end());
    for(int i = 0; i < I.size(); i++){
        column_map[I[i][0]].push_back(I[i][1]);
    }
    
    //printf("Columns : %d, %d\n",columns.size(),I.size());
            
    reply.resize(aggregation_queries);
    for(int i = 0; i < reply.size(); i++){
        //reply[i].resize(fd.size/BUFFER_SPACE);
    }
    bool flag =  false;
    for(int i = 0; i < fd.size/BUFFER_SPACE; i++){
        read_stream(fd,buff,buff.size());
        for(int j = 0;  j < buff.size(); j++){
            if(buff[j] != F(0)){
                flag = true;
                break;
            }
        }
        if(!flag) continue;

        //compute_tensorcode_linear_code(buff,tensor);
        //compute_tensorcode(buff,tensor);
        if(!linear_time){
            update_reply(buff,tensor,I,i,reply);
        }else{
            update_reply_spielman(buff,tensor,I,i,reply,columns,column_map);
        }
        //for(int k = 0; k < I.size(); k++){
        //    reply[k][i] = tensor[I[k][1]][I[k][0]];
        //}
        flag = false;
    }
    
}

bool compareFirstElement(const std::vector<size_t> &a, const std::vector<size_t> &b) {
    return a[0] < b[0];
}
void find_collumns(vector<vector<size_t>> &I, vector <size_t> &C, vector<vector<size_t>> &I_sorted){
    vector<int> I_t;
    I_sorted = I;
    for(int i = 0; i < I.size(); i++){
        I_t.push_back(I[i][0]);
    }
    std::sort(I_sorted.begin(), I_sorted.end(), compareFirstElement);
    std::sort(I_t.begin(),I_t.end());
    C.push_back(I_t[0]);
    for(int i = 1; i < I_t.size(); i++){
        if(I_t[i] != I_t[i-1]){
            C.push_back(I_t[i]);
        }
    }
}

int next_pow2(int l){
    if(l != 1ULL<<((int)log2(l))){
        return 1ULL<<((int)log2(l)+1);
    }
    return l;
}

void open_brakedown_stream(stream_descriptor fd , vector<F> x,  vector<vector<_hash>> &Commitment_MT){
    int queries = 2935;
    double ps = 0.0,vt = 0.0;
    vector<F> aggregated_vector1,aggregated_vector2;
    vector<F> x1,r_v;
    vector<F> beta;
    for(int i = 0; i < (int)log2(fd.size/BUFFER_SPACE); i++)x1.push_back(x[i]);
    precompute_beta(x1,beta);
    r_v.resize(beta.size());
    r_v[0] = generate_randomness(1)[0];
    for(int i = 1; i < r_v.size(); i++){
        r_v[i] = r_v[i-1]*r_v[0];
    }
    aggregate_brakedown(fd ,beta,r_v,aggregated_vector1,aggregated_vector2);
    vector<size_t> I(queries);
    for(int i = 0; i < I.size(); i++){
        I[i] = rand()%(2*BUFFER_SPACE);
    }
    vector<vector<F>> R(I.size());
    compute_reply(fd,I,R);
    
    vector<vector<_hash>> commitment_paths;
    vector<size_t> c(2);
    for(int i = 0; i < I.size(); i++){
        c[0] = 0;c[1] = I[i];
        commitment_paths.push_back(merkle_tree::merkle_tree_prover::open_tree_blake(Commitment_MT,c,0));
    }
    
    clock_t t1 = clock();
    vector<vector<_hash>> hashes;
    for(int i = 0; i < I.size(); i++){
        vector<F> temp  = R[i];
        pad_vector(temp);
        merkle_tree::merkle_tree_prover::MT_commit_Blake(temp.data(),hashes,temp.size());
        hashes.clear();
    }
    
    vector<F> code_beta(2*BUFFER_SPACE),code_r(2*BUFFER_SPACE);
    encode_monolithic(aggregated_vector1.data(),code_beta.data(),BUFFER_SPACE);
    encode_monolithic(aggregated_vector2.data(),code_r.data(),BUFFER_SPACE);
    for(int i = 0; i < I.size(); i++){
        F sum1 = F(0),sum2 = F(0);
        for(int j = 0; j < R[0].size(); j++){
            sum1 += r_v[j]*R[i][j];
            sum2 += beta[j]*R[i][j];
        }
    }
    bool *visited = new bool[2*Commitment_MT[0].size()];
    for(int i = 0; i <2*Commitment_MT[0].size(); i++){
        visited[i] = false;
    }
    
    for(int i = 0; i < I.size(); i++){
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(Commitment_MT,commitment_paths[i].data(),I[i],Commitment_MT[0].size(),visited,ps);    
    }
    
    clock_t t2 = clock();
    vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;
    ps += (double)(R.size()*R[0].size()*sizeof(F))/1024.0;
    ps += (2*BUFFER_SPACE*sizeof(F))/1024.0;
    printf("Ps : %lf, Vt : %lf\n",ps,vt);

}

void open(stream_descriptor fd , vector<F> x,  vector<vector<_hash>> &Commitment_MT, double &vt, double &ps){
    int queries = 5900;
    if(!linear_time){
        queries = 700;
    }
    
    vector<vector<_hash>> Aggregated_MT;
    vector<F> x1,x2;
    vector<F> r_v;
    vector<vector<F>> aggr_tensor;
    vector<F> aggr_vector;
    aggregation_queries = queries;
    
    for(int i = 0; i < (int)log2(fd.size/BUFFER_SPACE); i++){x1.push_back(x[i]);}
    for(int i = (int)log2(fd.size/BUFFER_SPACE); i < x.size(); i++){x2.push_back(x[i]);}
    vector<F> beta;

    precompute_beta(x1,beta);
    r_v.resize(beta.size());
    r_v[0] = generate_randomness(1)[0];
    for(int i = 1; i < r_v.size(); i++){
        r_v[i] = r_v[i-1]*r_v[0];
    }

    I.resize(queries);
    vector<size_t> I_v(queries);
    for(int i = 0; i < queries; i++){
        I[i].push_back(rand()%(2*BUFFER_SPACE/tensor_row_size));
        I[i].push_back(rand()%(2*tensor_row_size));
        I_v[i] = I[i][0] + (2*BUFFER_SPACE/tensor_row_size)*I[i][1];
    }

    clock_t t1,t2; 
    t1 = clock();
    aggregate(fd ,beta,r_v,Aggregated_MT,aggr_vector,aggr_tensor);
    t2 = clock();
   //printf("Aggr time : %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);
    
    
    //sleep(10);
    
    vector<vector<F>> reply;
    t1 = clock();
    compute_aggregation_reply(fd,I,reply);
    t2 = clock();
    //printf("Reply time: %lf\n",(double)(t2-t1)/(double)CLOCKS_PER_SEC);

    //printf(">> %d, %d\n",reply.size(),reply[0].size());
    vector<_hash> commitment_path;
    //vector<vector<__hhash_digest>> aggregated_commitment_paths;
    bool *visited = new bool[Commitment_MT[0].size()*2];
    for(int i = 0; i < Commitment_MT[0].size()*2; i++){
        visited[i] = false;
    }
   
    //clock_t t1,t2;
    double MT_ps = 0.0;
    t1 = clock();
    for(int i = 0; i  < I.size(); i++){
        vector<vector<_hash>> MT;
        merkle_tree::merkle_tree_prover::MT_commit_Blake(reply[i].data(),MT,reply[i].size());
    }
    for(int i = 0; i < I.size(); i++){
        commitment_path = merkle_tree::merkle_tree_prover::open_tree_blake(Commitment_MT,I[i],2*BUFFER_SPACE/tensor_row_size);
        merkle_tree::merkle_tree_verifier::verify_claim_opt_blake(Commitment_MT,commitment_path.data(),(I[i][1]/4)*2*BUFFER_SPACE/tensor_row_size+I[i][0],Commitment_MT[0].size(),visited,MT_ps);
    }
    t2 = clock();
    //printf("Opening proofs : %lf\n",MT_ps);
    for(int i = 0; i < Commitment_MT.size(); i++){
        Commitment_MT[i].clear();
        vector<_hash>(Commitment_MT[i]).swap(Commitment_MT[i]); 
    }
    Commitment_MT.clear();
    vector<vector<_hash>>(Commitment_MT).swap(Commitment_MT);
    delete[] visited;
    
    ps += (double)(reply.size()*reply[0].size()*sizeof(virgo::fieldElement))/1024.0;
    //double ps = 0.0,vt = 0.0;
    //printf(">> %lf Kb\n",(double)(reply.size()*reply[0].size()*sizeof(virgo::fieldElement))/1024.0);
    if(!linear_time){
        recursive_prover_RS(aggr_vector, I,vt,ps );
    }else{
        clock_t _t1,_t2;
        _t1 = clock();
        //printf("%d,%d,%d,%d\n",aggr_tensor.size(),aggr_tensor[0].size(),aux_commit.size(),aux_commit[0].size());
        recursive_prover_Spielman_stream(aggr_vector, aggr_tensor, aux_commit, I,vt , ps); 
        //recursive_prover_Spielman(aggr_vector,aggr_tensor,I_v,vt,ps );
        _t2 = clock();
        //printf("??? %lf\n",(double)(_t2-_t1)/(double)CLOCKS_PER_SEC); 
    }
    
    
    //printf("%lf\n",ps);
    ps += MT_ps;
    //Elastic_PC_ps += ps;
    vt += (double)(t2-t1)/(double)CLOCKS_PER_SEC;

    printf("PC : ps = %lf, vt = %lf\n",ps,vt);
    // Virgo Open 


}

void init_commitment(bool mod){
    linear_time = mod;
    tensor_row_size = BUFFER_SPACE/(1ULL<<(11));  
    if(tensor_row_size == 0){
        tensor_row_size = 16;
    }
}

void test_Elastic_PC(size_t N, int option){
    if(option == 1){
        linear_time = false;
        vector<vector<_hash>> hashes;
        _hash comm;
        vector<vector<_hash>> MT_hashes;
        stream_descriptor commit_data;commit_data.name = "test";commit_data.size = N;
        tensor_row_size = BUFFER_SPACE/(1ULL<<(11));
        
        auto start = std::chrono::steady_clock::now();    
        commit(commit_data, comm, MT_hashes);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        printf("Commitment finished\n");
        //sleep(5);
        double vt = 0.0,ps = 0.0;
        start = std::chrono::steady_clock::now();
        open(commit_data,generate_randomness((int)log2(N)),MT_hashes,vt,ps);
        end = std::chrono::steady_clock::now();

        // Calculate the elapsed time in seconds
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        printf("Total prover time : %lf\n",elapsed_seconds);
    }else if(option == 2){
        linear_time = true;
        int K = N/BUFFER_SPACE;
        tensor_row_size = N/(K*1ULL<<(14));
        printf("> %d\n",tensor_row_size);
        _hash comm;
        vector<vector<_hash>> MT_hashes;
        stream_descriptor commit_data;commit_data.name = "test";commit_data.size = N;

        expander_init_store(tensor_row_size);
        
        auto start = std::chrono::steady_clock::now();
        commit(commit_data, comm, MT_hashes);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        double vt = 0.0,ps = 0.0;
        start = std::chrono::steady_clock::now();
        open(commit_data,generate_randomness((int)log2(N)),MT_hashes,vt,ps);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
    }else{
        int n = (int)log2(N);
        if(n%2){
            BUFFER_SPACE = 1ULL<<(n/2+6);
        }
        else{
            BUFFER_SPACE = 1ULL<<((n-1)/2+6);
        }
        vector<vector<_hash>> MT_hashes;
        stream_descriptor commit_data;commit_data.name = "test";commit_data.size = N;
        expander_init_store(BUFFER_SPACE);
        auto start = std::chrono::steady_clock::now();
        commit_brakedown_stream(commit_data,MT_hashes);
        auto end = std::chrono::steady_clock::now();
        auto elapsed_seconds = std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        double commit_time = elapsed_seconds;
        std::cout << "Commit time: " << commit_time << " seconds" << std::endl;
        start = std::chrono::steady_clock::now();
        open_brakedown_stream(commit_data,generate_randomness(n),MT_hashes);
        end = std::chrono::steady_clock::now();
        elapsed_seconds += std::chrono::duration_cast<std::chrono::duration<double>>(end - start).count();
        std::cout << "Total time: " << elapsed_seconds << " seconds" << std::endl;
        
    }
}