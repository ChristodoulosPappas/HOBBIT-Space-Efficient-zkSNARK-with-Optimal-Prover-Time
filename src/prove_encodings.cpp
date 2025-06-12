#include "prove_encodings.h"
#include "math.h"

extern double commit_timer;
zk_prover prover;
zk_verifier verifier;
std::map<long long, long long> _gates_count;
std::pair<long long, long long> _prepare_enc_count(long long input_size, long long output_size_so_far, int copies ,int depth)
{
    if(input_size <= distance_threshold)
    {
        return std::make_pair(depth, output_size_so_far);
    }
    //output
    //printf("%d: %d,%d,%d\n",depth + 1,output_size_so_far , input_size, C[depth].R);
    _gates_count[depth + 1] = output_size_so_far + input_size + _C[depth].R;
    auto output_depth_output_size = _prepare_enc_count(_C[depth].R, output_size_so_far + input_size,copies, depth + 1);
    _gates_count[output_depth_output_size.first + 1] = output_depth_output_size.second + D[depth].R;
    //printf(">> %d: %d,%d\n",output_depth_output_size.first + 1,output_depth_output_size.second , D[depth].R);
    return std::make_pair(output_depth_output_size.first + 1, _gates_count[output_depth_output_size.first + 1]);
}

int _smallest_pow2_larger_or_equal_to(int x)
{
    for(int i = 0; i < 32; ++i)
    {
        if((1 << i) >= x)
            return (1 << i);
    }
    assert(false);
}

void _prepare__gates_count(long long *query, long long N, int copies, int query_count)
{
    long long query_ptr = 0;
    //input _layer
    _gates_count[0] = copies*N;

    //expander part
    _gates_count[1] = N + _C[0].R;
    std::pair<long long, long long> output_depth_output_size = _prepare_enc_count(_C[0].R, N, copies, 1);

    _gates_count[output_depth_output_size.first + 1] = N + output_depth_output_size.second + D[0].R;
    for(int i = 1; i < output_depth_output_size.first + 2; i++){
        _gates_count[i] = copies*_gates_count[i];
    }
    _gates_count[output_depth_output_size.first + 2] = query_count;
}

std::pair<long long, long long> _generate_enc_circuit(long long input_size, long long output_size_so_far, long long recursion_depth, long long input_depth, int copies)
{

    if(input_size <= distance_threshold)
    {
        return std::make_pair(input_depth, output_size_so_far);
    }
    //relay the output
    for(int i = 0; i < copies*output_size_so_far; ++i)
    {
        verifier.C.circuit[input_depth + 1].gates[i] = _gate(gate_types::relay, i, 0);
    }
    verifier.C.circuit[input_depth + 1].weight_expander_C_mempool = new prime_field::field_element[cn * _C[recursion_depth].L];
    verifier.C.circuit[input_depth + 1].src_expander_C_mempool = (int *)malloc((int)(cn * _C[recursion_depth].L)*sizeof(int));
    //new int[cn * _C[recursion_depth].L];
    //verifier.C.circuit[input_depth + 1].weight_expander_C_mempool = new prime_field::field_element[cn * _C[recursion_depth].L];
    
    for(int k = 0; k  < copies; k++){   
        int mempool_ptr = 0;
        for(int i = 0; i < _C[recursion_depth].R; ++i)
        {
            int neighbor_size = _C[recursion_depth].r_neighbor[i].size();
            verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i + _C[recursion_depth].R*k].ty = gate_types::custom_linear_comb;
            verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i+ _C[recursion_depth].R*k].parameter_length = neighbor_size;
            verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i+ _C[recursion_depth].R*k].src = &verifier.C.circuit[input_depth + 1].src_expander_C_mempool[mempool_ptr];
            verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i+ _C[recursion_depth].R*k].weight = &verifier.C.circuit[input_depth + 1].weight_expander_C_mempool[mempool_ptr];
            mempool_ptr += _C[recursion_depth].r_neighbor[i].size();
            int C_input_offset = output_size_so_far - input_size;
            for(int j = 0; j < neighbor_size; ++j)
            {
                verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i + _C[recursion_depth].R*k].src[j] = _C[recursion_depth].r_neighbor[i][j] + C_input_offset;
                verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i + _C[recursion_depth].R*k].weight[j].real = _C[recursion_depth].r_weight[i][j].real;
                verifier.C.circuit[input_depth + 1].gates[copies*output_size_so_far + i + _C[recursion_depth].R*k].weight[j].img = _C[recursion_depth].r_weight[i][j].img;
            }
        }
    }
    auto output_depth_output_size = _generate_enc_circuit(_C[recursion_depth].R, output_size_so_far + _C[recursion_depth].R, recursion_depth + 1, input_depth + 1,copies);
    long long D_input_offset = output_size_so_far;

    long long final_output_depth = output_depth_output_size.first + 1;

    output_size_so_far = output_depth_output_size.second;
    
    
     //relay the output
    for(long long i = 0; i < copies*output_size_so_far; ++i)
    {
        verifier.C.circuit[final_output_depth].gates[i] = _gate(gate_types::relay, i, 0);
    }

    verifier.C.circuit[final_output_depth].src_expander_D_mempool = new int[dn * D[recursion_depth].L];
    verifier.C.circuit[final_output_depth].weight_expander_D_mempool = new prime_field::field_element[dn * D[recursion_depth].L];

    for(int k = 0; k < copies; k++){
        int mempool_ptr = 0;
        for(long long i = 0; i < D[recursion_depth].R; ++i)
        {
            long long neighbor_size = D[recursion_depth].r_neighbor[i].size();
            verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i + k*D[recursion_depth].R].ty = gate_types::custom_linear_comb;
            verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i + k*D[recursion_depth].R].parameter_length = neighbor_size;
            verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i+ k*D[recursion_depth].R].src = &verifier.C.circuit[final_output_depth].src_expander_D_mempool[mempool_ptr];
            verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i+ k*D[recursion_depth].R].weight = &verifier.C.circuit[final_output_depth].weight_expander_D_mempool[mempool_ptr];
            mempool_ptr += D[recursion_depth].r_neighbor[i].size();
            for(long long j = 0; j < neighbor_size; ++j)
            {
                verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i+ k*D[recursion_depth].R].src[j] = D[recursion_depth].r_neighbor[i][j] + D_input_offset;
                verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i+ k*D[recursion_depth].R].weight[j].real = D[recursion_depth].r_weight[i][j].real;
                verifier.C.circuit[final_output_depth].gates[copies*output_size_so_far + i+ k*D[recursion_depth].R].weight[j].img = D[recursion_depth].r_weight[i][j].img;
            }
        }
    }
    
    return std::make_pair(final_output_depth, output_size_so_far + D[recursion_depth].R);
}

void _generate_circuit(long long* query, long long N, int query_count, int copies, prime_field::field_element *input)
{
    std::sort(query, query + query_count);
    
    _prepare__gates_count(query, N, copies, query_count);
    
    verifier.C.inputs = new prime_field::field_element[N*copies];
    verifier.C.total_depth = _gates_count.size() + 2;
    verifier.C.circuit = new _layer[verifier.C.total_depth];
    verifier.C.circuit[0].bit_length = mylog(N*copies);
    verifier.C.circuit[0].gates = new _gate[1LL << verifier.C.circuit[0].bit_length];
    
    for(int i = 0; i < _gates_count.size(); ++i)
    {
        verifier.C.circuit[i + 1].bit_length = mylog(_smallest_pow2_larger_or_equal_to(_gates_count[i]));
        verifier.C.circuit[i + 1].gates = new _gate[1LL << verifier.C.circuit[i + 1].bit_length];
    }

    verifier.C.circuit[_gates_count.size() + 1].bit_length = mylog(_smallest_pow2_larger_or_equal_to(query_count));
    verifier.C.circuit[_gates_count.size() + 1].gates = new _gate[1LL << verifier.C.circuit[_gates_count.size() + 1].bit_length];

    for(long long i = 0; i < copies*N; ++i)
    {
        verifier.C.inputs[i] = input[i];
        verifier.C.circuit[0].gates[i] = _gate(gate_types::input, 0, 0);
        verifier.C.circuit[1].gates[i] = _gate(gate_types::direct_relay, i, 0);
    }
 
    for(long long i = 0; i < copies*N; ++i)
    {
        verifier.C.circuit[2].gates[i] = _gate(gate_types::relay, i, 0);
    }
 
    verifier.C.circuit[2].src_expander_C_mempool = new int[cn * _C[0].L];
    verifier.C.circuit[2].weight_expander_C_mempool = new prime_field::field_element[cn * _C[0].L];
    for(int k = 0; k < copies; k++){
        int C_mempool_ptr = 0, D_mempool_ptr = 0;
        for(long long i = 0; i < _C[0].R; ++i)
        {
            verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R] = _gate(gate_types::custom_linear_comb, 0, 0);
            verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R].parameter_length = _C[0].r_neighbor[i].size();
            verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R].src = &verifier.C.circuit[2].src_expander_C_mempool[C_mempool_ptr];
            verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R].weight = &verifier.C.circuit[2].weight_expander_C_mempool[C_mempool_ptr];
            C_mempool_ptr += _C[0].r_neighbor[i].size();
            for(long long j = 0; j < _C[0].r_neighbor[i].size(); ++j)
            {
                long long L = _C[0].r_neighbor[i][j];
                long long R = i;
                prime_field::field_element weight;
                weight.img = _C[0].r_weight[R][j].img;
                weight.real = _C[0].r_weight[R][j].real;
                verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R].src[j] = L;
                verifier.C.circuit[2].gates[i + copies*N + k*_C[0].R].weight[j] = weight;
            }
        }
        
    }
     
    auto output_depth_output_size = _generate_enc_circuit(_C[0].R, N + _C[0].R, 1, 2, copies);
    
    //add final output
    long long final_output_depth = output_depth_output_size.first + 1;
    
    for(long long i = 0; i < output_depth_output_size.second*copies; ++i)
    {
        verifier.C.circuit[final_output_depth].gates[i] = _gate(gate_types::relay, i, 0);
    }

    long long D_input_offset = N;
    long long output_so_far = output_depth_output_size.second;
    verifier.C.circuit[final_output_depth].src_expander_D_mempool = new int[dn * D[0].L];
    verifier.C.circuit[final_output_depth].weight_expander_D_mempool = new prime_field::field_element[dn * D[0].L];
    int C_mempool_ptr = 0, D_mempool_ptr = 0;
    for(int k = 0; k < copies; k++){
        C_mempool_ptr = 0; D_mempool_ptr = 0;
        for(long long i = 0; i < D[0].R; ++i)
        {
            verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i + D[0].R*k].ty = gate_types::custom_linear_comb;
            verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].parameter_length = D[0].r_neighbor[i].size();
            verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].src = &verifier.C.circuit[final_output_depth].src_expander_D_mempool[D_mempool_ptr];
            verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].weight = &verifier.C.circuit[final_output_depth].weight_expander_D_mempool[D_mempool_ptr];
            D_mempool_ptr += D[0].r_neighbor[i].size();
            for(long long j = 0; j < D[0].r_neighbor[i].size(); ++j)
            {
                verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].src[j] = D[0].r_neighbor[i][j] + N;
                verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].weight[j].img = D[0].r_weight[i][j].img;
                verifier.C.circuit[final_output_depth].gates[copies*output_so_far + i+ D[0].R*k].weight[j].real = D[0].r_weight[i][j].real;
            }
        }
    }
    

    for(long long i = 0; i < query_count; ++i)
    {
        verifier.C.circuit[final_output_depth + 1].gates[i] = _gate(gate_types::relay, query[i], 0);
    }
    assert(C_mempool_ptr == cn * _C[0].L);
}




void prove_encodings_orion(vector<vector<F>> vectors, vector<size_t> J){
    
    long long *q = new long long[J.size()];
    for(int i = 0; i < J.size(); i++){
        q[i] = J[i];
    }
   
   
    prime_field::field_element *coefs = new prime_field::field_element[vectors.size()*vectors[0].size()];
    for(int i  = 0; i < vectors.size()*vectors[0].size(); i++){
        coefs[i] = prime_field::field_element(i+32);
    }
  
    /*
    printf("%d\n",vectors.size()*vectors[0].size());
    for(int i = 0; i < vectors.size(); i++){
        for(int j = 0; j < vectors[i].size(); j++){
            coefs[i*vectors[i].size() + j].real = vectors[i][j].real;
            coefs[i*vectors[i].size() + j].img = vectors[i][j].img;
        }
    }
   
    printf("%d,%d\n",vectors.size(),vectors[0].size());
    */
    _generate_circuit(q, vectors[0].size(), J.size(),vectors.size(), coefs);
    verifier.get_prover(&prover);
    prover.get_circuit(verifier.C);
    int max_bit_length = -1;
    for(int i = 0; i < verifier.C.total_depth; ++i)
        max_bit_length = max(max_bit_length, verifier.C.circuit[i].bit_length);
    prover.init_array(max_bit_length);
    verifier.init_array(max_bit_length);
    prover.get_witness(coefs, vectors[0].size());

    bool result1 = verifier.verify("log.txt");

    printf(">>OK\n");

    free(coefs);
}



