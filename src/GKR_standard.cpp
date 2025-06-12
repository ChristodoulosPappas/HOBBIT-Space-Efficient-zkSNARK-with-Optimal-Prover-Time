#include "GKR_standard.h"
#include "inputCircuit.hpp"
//#include <fstream> 
//#include <queue> 
//#include <regex>
#include "config_pc.hpp"

using namespace std;
using std::max;
#define Clients 2
#define Len 8
extern int partitions;

vector<DAG_gate *> _in_circuit_dag;
vector<vector<DAG_gate *>> _ip_circuit_dag;




using std::cerr;
using std::endl;





layeredCircuit _DAG_to_layered() {
     layeredCircuit c;
     vector<u64> in_deg(_in_circuit_dag.size());          // in degree
    vector<int> lyr_id(_in_circuit_dag.size());          // the layer of each gate
    vector<u64> id_in_lyr(_in_circuit_dag.size());       // the corresponding id within the layer
    vector<vector<u64>> edges(_in_circuit_dag.size());   // the edges in the DAG

    // Topologically sorting
    queue<u64> q;
    for (u64 i = 0; i < _in_circuit_dag.size(); ++i) {

        auto &g = *_in_circuit_dag[i];
        if (g.input0.first == 'V') {
            ++in_deg[i];
            edges[g.input0.second].push_back(i);
        }
        if (g.input1.first == 'V') {
            ++in_deg[i];
            edges[g.input1.second].push_back(i);
        }
        if (g.ty == Input) {
            lyr_id[i] = 0;
            q.push(i);
        }
    }

    int max_lyr_id = 0;
    while (!q.empty()) {

        u64 u = q.front();
        q.pop();
        max_lyr_id = max(lyr_id[u], max_lyr_id);
        for (auto v: edges[u])
            if (!(--in_deg[v])) {
                q.push(v);
                lyr_id[v] = max(lyr_id[v], lyr_id[u] + 1);
            }
    }

    // build the circuit
    c.circuit.resize(max_lyr_id + 1);
    c.size = max_lyr_id + 1;
    for (u64 i = 0; i < _in_circuit_dag.size(); ++i)
        id_in_lyr[i] = c.circuit[lyr_id[i]].size++;

    for (int i = 0; i < c.size; ++i)
        c.circuit[i].gates.resize(c.circuit[i].size);

    for (u64 i = 0; i < _in_circuit_dag.size(); ++i) {
        int lg = lyr_id[i];
        u64 gid = id_in_lyr[i];
        auto &g = *_in_circuit_dag[i];
        auto ty = g.ty, nty = ty;
        u64 in0 = g.input0.second;
        u64 in1 = g.input1.second;
        bool is_assert = g.is_assert;
        u64 u, v;
        F cst;

        switch (ty) {
            case Mul: case Add: case Xor:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert);
                break;
            case AddMul:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                c.circuit[lg].gates[gid] = gate(ty, lyr_id[in1], u, v, F_ZERO, is_assert,0);
                for(int k = 0; k < _ip_circuit_dag[i].size()-1; k++){
                    auto &g_new = *_ip_circuit_dag[i][k];
                    u64 i0 = g_new.input0.second;
                    u64 i1 = g_new.input1.second;
                    u = id_in_lyr[i0];
                    v = id_in_lyr[i1];
                    if (lyr_id[in0] < lg - 1) swap(u, v), swap(in0, in1);
                    c.circuit[lg].gates[gid].push_elements(u,v);
                }
                break;
            case Sub:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiSub;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Naab:
                u = id_in_lyr[in0];
                v = id_in_lyr[in1];
                if (lyr_id[in0] < lg - 1) {
                    nty = AntiNaab;
                    swap(u, v);
                    swap(in0, in1);
                }
                c.circuit[lg].gates[gid] = gate(nty, lyr_id[in1], u, v, F_ZERO, is_assert);
            break;
            case Mulc: case Addc:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            break;
            case Not: case Copy:
                u = id_in_lyr[in0];
                cst = F(in1);
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, cst, is_assert);
            case Input:
                u = in0;
                c.circuit[lg].gates[gid] = gate(ty, -1, u, 0, F_ZERO, is_assert);
        }
    }
    // repeat the layer except the input for ${repeat} times
    for (int i = 1; i < c.size; ++i) {
        for (int j = 1; j < 1; ++j)
            for (u64 k = 0; k < c.circuit[i].size; ++k) {
                auto &g = c.circuit[i].gates[k];
                c.circuit[i].gates.push_back(c.circuit[i].gates[k]);
                if (g.ty != Input && i > 1) g.u += j * c.circuit[i].size;
                if (g.ty == Add ||
                    g.ty == Mul ||
                    g.ty == Xor ||
                    g.ty == AddMul ||
                    g.ty == Sub ||
                    g.ty == AntiSub ||
                    g.ty == Naab ||
                    g.ty == AntiNaab)
                    g.v += j * c.circuit[i].size;
            }
        c.circuit[i].size *= 1;
    }

    for (int i = 0; i <= max_lyr_id; ++i) {
        c.circuit[i].bitLength = (int) log2(c.circuit[i].size);
        if ((1ULL << c.circuit[i].bitLength) < c.circuit[i].size) ++c.circuit[i].bitLength;
    }
    return c;
}

#define REL 1

extern layeredCircuit _DAG_to_layered();

void parse(ifstream &circuit_in,long long int *in);

void parse_matrix_evaluations(ifstream &circuit_in,long long int *in, int sizes, int b1_size,int b2_size, int read_write_size);
void parse_test(ifstream &circuit_in,long long int *in, int N);


struct proof prove_matrix_evaluations(vector<F> &data, vector<F> randomness,   int sizes, int b1_size,int b2_size, int read_write_size){
    layeredCircuit c;
    char *input_file,*circuit_name;
    long long int *in;
    

    in = (long long int *)malloc(16*sizeof(long long int));
    for(int i = 0; i < 16; i++){
        in[i] = i;
    }

    ifstream circuit_in;
    _in_circuit_dag.clear();
    parse_matrix_evaluations(circuit_in,in, sizes, b1_size,b2_size, read_write_size);
    
    c = _DAG_to_layered();
    
    c.subsetInit();
    prover p(c,input_file,data,false);

    //printf("Prover initialized\n");
    verifier v(&p, c);
    //_ip_circuit_dag.clear();
    struct proof Pr = v.verify(randomness);
     for(int i = 0; i < _ip_circuit_dag.size(); i++){
        for(int j = 0; j < _ip_circuit_dag[i].size(); j++){
                    if(!_ip_circuit_dag[i][j]){
                delete _ip_circuit_dag[i][j];
            }
        }
        vector<DAG_gate*>().swap(_ip_circuit_dag[i]);
    }
    vector<vector<DAG_gate*>>().swap(_ip_circuit_dag);
    for(int i = 0; i <  _in_circuit_dag.size(); i++){
        if(!_in_circuit_dag[i]){
            delete _in_circuit_dag[i];
        }
    }
    vector<DAG_gate*>().swap(_in_circuit_dag);
    _ip_circuit_dag.clear();
    p.delete_data();
    c.delete_data();
    return Pr;
}


regex _add_gate("P V[0-9]+ = V[0-9]+ \\+ V[0-9]+ E");
regex _mult_gate("P V[0-9]+ = V[0-9]+ \\* V[0-9]+ E");
regex _add_mul_gate("P V[0-9]+ = V[0-9]+ ip V[0-9]+ E");
regex _input_gate("P V[0-9]+ = I[0-9]+ E");
regex _output_gate("P O[0-9]+ = V[0-9]+ E");
regex _xor_gate("P V[0-9]+ = V[0-9]+ XOR V[0-9]+ E");
regex _minus_gate("P V[0-9]+ = V[0-9]+ minus V[0-9]+ E");
regex _naab_gate("P V[0-9]+ = V[0-9]+ NAAB V[0-9]+ E");
regex _not_gate("P V[0-9]+ = V[0-9]+ NOT V[0-9]+ E");


smatch _base_match;

DAG_gate *_buildGate(gateType ty, u64 tgt, u64 src0, u64 src1 = -1, bool has_constant = true);
DAG_gate *_buildInput(u64 tgt, u64 src0);
void _setAssertion(u64 tgt);


void _add(int x,int y,int &counter){
    _buildGate(Add, counter, x,y, false);
    counter+=1;
}


int _sum_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            _add(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return _sum_tree(vec,counter);
    }
} 


void _mul(int x,int y,int &counter){
    _buildGate(Mul, counter, x,y, false);
    counter+=1;
}

void _sub(int x,int y,int &counter){
    _buildGate(Sub,counter,x,y,false);
    counter+=1;
}

void _ip(vector<int> x, vector<int> y, int &counter){
    for(int i = 0; i < x.size(); i++){
       
         _buildGate(AddMul,counter,x[i],y[i],false);
    }
    counter+=1;
}



int _mul_tree(vector<int> leaves,int &counter){
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            _mul(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return _mul_tree(vec,counter);
    }
}

int _add_tree(vector<int> leaves,int &counter){
    
    vector<int> vec;
    for(int i = 0; i < leaves.size(); i+=2){
        if(i+1 >= leaves.size()){
            vec.push_back(leaves[i]);
        }
        else{
            _add(leaves[i],leaves[i+1],counter);
            vec.push_back(counter-1);
        }
    }
    if(vec.size()==1){
        return vec[0];
    }
    else{
        return _add_tree(vec,counter);
    }
}


void parse_matrix_evaluations(ifstream &circuit_in,long long int *in, int matrix_size, int b1_size,int b2_size, int read_write_size){
    
    vector<int> read_write_transcript(read_write_size);
    vector<int> initial_transcript(b1_size*2);
    vector<int> final_accesses1(b1_size);
    vector<int> final_accesses2(b2_size);
    vector<int> indexes(b1_size);
    vector<int> beta1(b1_size);
    vector<int> beta2(b2_size);
    vector<vector<int>> matrix(matrix_size);
    int counter = 0;
    for(int i = 0; i < matrix_size; i++){
        matrix[i].resize(5);
        _buildInput(counter,0);
        matrix[i][0] = (counter);
        counter++;
        _buildInput(counter,0);
        matrix[i][1] = (counter);
        counter++;
        _buildInput(counter,0);
        matrix[i][2] = (counter);
        counter++;
        _buildInput(counter,0);
        matrix[i][3] = (counter);
        counter++;
        _buildInput(counter,0);
        matrix[i][4] = (counter);
        counter++;
    }
    for(int i = 0; i < b1_size; i++){
        _buildInput(counter,0);
        final_accesses1[i] = (counter);
        counter++;    
    }
    for(int i = 0; i < b2_size; i++){
        _buildInput(counter,0);
        final_accesses2[i] = (counter);
        counter++;    
    }
    for(int i = 0; i < read_write_size; i++){
        _buildInput(counter,0);
        read_write_transcript[i] = (counter);
        counter++;    
    }
    for(int i = 0; i  < b1_size; i++){
        _buildInput(counter,0);
        indexes[i] = counter;
        counter++;    
    }
    for(int i = 0; i < b1_size; i++){
        _buildInput(counter,0);
        beta1[i] = (counter);
        counter++;    
    }
    for(int i = 0; i < b2_size; i++){
        _buildInput(counter,0);
        beta2[i] = (counter);
        counter++;    
    }
    int zero = counter;
    _buildInput(counter,0);
    counter++;
    int one = counter;
    _buildInput(counter,0);
    counter++;
    int a = counter;
    _buildInput(counter,0);
    counter++;
    int b = counter;
    _buildInput(counter,0);
    counter++;
    
    
    vector<int> Rs(read_write_size/2),Ws(read_write_size/2),Is(b1_size),Fs(b1_size);
    vector<int> buff(3);
    vector<int> hash(3);hash[0] = one;hash[1] = a;hash[2] = b;
    
    for(int i = 0; i < matrix.size(); i++){
        buff[0] = matrix[i][0];
        _sub(matrix[i][1],one,counter);
        buff[1] = counter-1;
        buff[2] = read_write_transcript[2*i];
        _ip(buff,hash,counter);
        Rs[i] = counter-1;
        buff[0] = matrix[i][0];
        buff[1] = matrix[i][1];
        buff[2] = read_write_transcript[2*i];
        _ip(buff,hash,counter);
        Ws[i] = counter-1;
    }
    for(int i = 0; i  < b1_size; i++){
        buff[0] = indexes[i];
        buff[1] = zero;
        buff[2] = beta1[i];
        _ip(buff,hash,counter);
        Is[i] = counter-1;
    }
    for(int i = 0; i  < b1_size; i++){
        buff[0] = indexes[i];
        buff[1] = final_accesses1[i];
        buff[2] = beta1[i];
        _ip(buff,hash,counter);
        Fs[i] = counter-1;
    }
    _mul_tree(Ws,counter);
    int out1 = counter-1;
    _mul_tree(Rs,counter);
    int out2 = counter-1;
    _mul_tree(Is,counter);
    int out3 = counter-1;
    _mul_tree(Fs,counter);
    int out4 = counter-1;
    
    for(int i = 0; i < matrix.size(); i++){
        buff[0] = matrix[i][2];
        _sub(matrix[i][3],one,counter);
        buff[1] = counter-1;
        buff[2] = read_write_transcript[2*i+1];
        _ip(buff,hash,counter);
        Rs[i] = counter-1;
        buff[0] = matrix[i][2];
        buff[1] = matrix[i][3];
        buff[2] = read_write_transcript[2*i+1];
        _ip(buff,hash,counter);
        Ws[i] = counter-1;
    }
    Is.resize(b2_size);Fs.resize(b2_size);
    for(int i = 0; i  < b2_size; i++){
        buff[0] = indexes[i];
        buff[1] = zero;
        buff[2] = beta2[i];
        _ip(buff,hash,counter);
        Is[i] = counter-1;
    }
    for(int i = 0; i  < b2_size; i++){
        buff[0] = indexes[i];
        buff[1] = final_accesses2[i];
        buff[2] = beta2[i];
        _ip(buff,hash,counter);
        Fs[i] = counter-1;
    }
    _mul_tree(Ws,counter);
    out1 = counter-1;
    _mul_tree(Rs,counter);
    out2 = counter-1;
    _mul_tree(Is,counter);
    out3 = counter-1;
    _mul_tree(Fs,counter);
    out4 = counter-1;
    vector<int> v1(matrix.size()),v2(matrix.size());
    for(int i = 0; i < matrix.size(); i++){
        _mul(read_write_transcript[2*i],read_write_transcript[2*i+1],counter);
        v1[i] = counter-1;
        v2[i] = matrix[i][4];
    }
    _ip(v1,v2,counter);
}





void _parse(ifstream &circuit_in, long long int *in) {
    string source_line;
    i64 tgt, src0, src1;
    
    while (getline(circuit_in, source_line)) {
        if (std::regex_match(source_line, _base_match, _add_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld + V%lld E", &tgt, &src0, &src1);
            _buildGate(Add, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _mult_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld * V%lld E", &tgt, &src0, &src1);
            _buildGate(Mul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _input_gate)) {
            sscanf(source_line.c_str(), "P V%lld = I%lld E", &tgt, &src0);
            _buildInput(tgt, 0);
        } else if (std::regex_match(source_line, _base_match, _output_gate)) {
            sscanf(source_line.c_str(), "P O%lld = V%lld E", &tgt, &src0);
        } else if (std::regex_match(source_line, _base_match, _xor_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld XOR V%lld E", &tgt, &src0, &src1);
            _buildGate(Xor, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _add_mul_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld ip V%lld E", &tgt, &src0, &src1);
            _buildGate(AddMul, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _naab_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NAAB V%lld E", &tgt, &src0, &src1);
            _buildGate(Naab, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _minus_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld minus V%lld E", &tgt, &src0, &src1);
            _buildGate(Sub, tgt, src0, src1, false);
        } else if (std::regex_match(source_line, _base_match, _not_gate)) {
            sscanf(source_line.c_str(), "P V%lld = V%lld NOT V%lld E", &tgt, &src0, &src1);
            _buildGate(Not, tgt, src0, 0, true);
        } else {
            assert(false);
        }
    }
    //free(in);
}

DAG_gate *_buildGate(gateType ty, u64 tgt, u64 src0, u64 src1, bool has_constant) {

    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v; 
    g->is_assert = false;
    g->ty = ty;
    g->input0 = make_pair((int)'V', src0);
    g->input1 = make_pair(has_constant ? (int)'S' : 'V', src1);
    if (tgt >= _in_circuit_dag.size()){

        _in_circuit_dag.resize(tgt + 1, nullptr);
    }
    if (tgt >= _ip_circuit_dag.size()) {
        _ip_circuit_dag.resize(tgt + 1,v);
    }
    _in_circuit_dag[tgt] = g;
    if(ty == AddMul){
        _ip_circuit_dag[tgt].resize(_ip_circuit_dag[tgt].size() + 1,nullptr);
        _ip_circuit_dag[tgt][_ip_circuit_dag[tgt].size()-1] = g;
    }
    
    
    return g;
}

DAG_gate *_buildInput(u64 tgt, u64 src0) {
//  fprintf(stderr, "_buildInput: tgt: %d, src0: %d\n", tgt, src0);
    DAG_gate *g = new DAG_gate();
    vector<DAG_gate *> v;
    g->is_assert = false;
    g->ty = Input;
    g->input0 = make_pair((int)'S', src0);
    g->input1 = make_pair((int)'N', 0);
    if (tgt >= _in_circuit_dag.size()) _in_circuit_dag.resize(tgt + 1, nullptr);
    if (tgt >= _in_circuit_dag.size()) _ip_circuit_dag.resize(tgt + 1, v);
    
    _in_circuit_dag[tgt] = g;
    return g;
}

void _setAssertion(u64 tgt) {
    assert(tgt < _in_circuit_dag.size());
    _in_circuit_dag[tgt]->is_assert = true;
}