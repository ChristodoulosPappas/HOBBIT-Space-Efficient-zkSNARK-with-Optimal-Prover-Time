
#include "witness_stream.h"
#include "Seval.h"
extern layeredCircuit C;

extern vector<F> beta11,beta12,beta13,beta14;
extern vector<F> beta22;
extern vector<F> a;
extern int mod;
extern vector<unsigned int> preimage;
extern vector<unsigned int> SHA;
extern vector<int> H;
extern vector<F> V_in;
extern int Circuits;
extern int BUFFER_SPACE_tr;
extern size_t circuit_size;
extern mutex mtx,mtx2;
extern tr_tuple *tr;
extern vector<vector<int>> lookup_table;
vector<vector<int>> access_table;
extern vector<F> lookup_rand;
extern size_t gates,ops;
extern bool has_lookups;

vector<unsigned int> rotate(vector<unsigned int> bits, int shift){
	vector<unsigned int> new_bits;
 	for(int i = shift; i < bits.size(); i++){
        new_bits.push_back(bits[i]);
    }
    for(int i = 0; i < shift; i++){
        new_bits.push_back(bits[i]);
    }
	return new_bits;
}

vector<unsigned int> shift(vector<unsigned int> bits, int shift){
	vector<unsigned int> new_bits;
	for(int i = shift; i < bits.size(); i++){
		new_bits.push_back(bits[i]);
	}
	for(int i = 0; i < bits.size()-shift; i++){
		new_bits.push_back((0));
	}
	return new_bits;
}

vector<unsigned int> prepare_bit_vector(unsigned int word, int range){
    vector<unsigned int> bits(range,0);
    for(int i = 0; i < range; i++){
        if(word&1){
            bits[i] = 1;
        }
        word = word>>1;
    }
    return bits;
}

vector<F> get_sha_witness(vector<unsigned int> words){
	vector<F> gkr_input;
	vector<unsigned long int> pow(32);pow[0] = 1;pow[1] = 2;
	for(int i = 2; i < 32; i++){
		pow[i] = pow[i-1]*pow[1];
	}
	vector<F> new_words(48);
	vector<vector<unsigned int>> words_bits(64);
	vector<F> buff;
	for(int i = 0; i < 16; i++){
		words_bits[i] = prepare_bit_vector(words[i], 32);
	}
	vector<F> quotients;

	for(int i = 0;i < 16; i++){
		quotients.push_back(F_ZERO);
	}
	for(int i = 16; i < 64; i++){
		unsigned long long int temp_word1 = 0,temp_word2 = 0;
		vector<unsigned int> w1 = rotate(words_bits[i-15],7);
		vector<unsigned int> w2 = rotate(words_bits[i-15],18);
		vector<unsigned int> w3 = shift(words_bits[i-15],3);
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			temp_word1 = temp_word1 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		
		w1 = rotate(words_bits[i-2],17);
		w2 = rotate(words_bits[i-2],19);
		w3 = shift(words_bits[i-2],10);
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			temp_word2 = temp_word2 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		unsigned long long int temp_word = temp_word1 + temp_word2 + words[i - 16] + words[i-7];
		quotients.push_back(temp_word/((unsigned long long)1ULL<<32));
		words.push_back(temp_word%((unsigned long long)1ULL<<32));
		
		//printf("OK %d,%d,%d,%lld,%lld\n",i,buff.size(),words.size(),1ULL<<32, words[i].toint128());
		words_bits[i] = prepare_bit_vector(words[i], 32);
		if(words_bits[i].size() != 32){
			printf("Error in witness 0\n");
			exit(-1);
		}
	}

	
	vector<unsigned int> a(65),b(65),c(65),d(65),e(65),f(65),g(65),h(65);
    a[0] = H[0];b[0] = H[1];c[0] = H[2];d[0] = H[3];
	e[0] = H[4];f[0] = H[5];g[0] = H[6];h[0] = H[7];
	vector<vector<unsigned int>> a_bits(64),b_bits(64),c_bits(64),e_bits(64),f_bits(64),g_bits(64);
    vector<unsigned long long int> a_q,e_q;

    for(int i = 0; i < 64; i++){
		
        a_bits[i] = prepare_bit_vector(a[i],32);
		
        unsigned long long int s0 = 0;
		vector<unsigned int> w1 = rotate(a_bits[i],2);
		vector<unsigned int> w2 = rotate(a_bits[i],13);
		vector<unsigned int> w3 = rotate(a_bits[i],22);
		
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			s0 = s0+ pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		buff.push_back(b[i]);
		b_bits[i] = prepare_bit_vector(b[i],32);
		buff.clear();
		buff.push_back(c[i]);
		c_bits[i] = prepare_bit_vector(c[i],32);
		buff.clear();	
		if(a_bits[i].size() != 32 || b_bits[i].size() != 32 || c_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		unsigned long long int maj = 0;
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = a_bits[i][j]*b_bits[i][j] + b_bits[i][j]*c_bits[i][j] - 2*a_bits[i][j]*b_bits[i][j]*b_bits[i][j]*c_bits[i][j];
			maj = maj + pow[j]*(c_bits[i][j]*a_bits[i][j] + _t - 2*c_bits[i][j]*a_bits[i][j]*_t);
		}
		unsigned long long int t2 = maj + s0;
		
        e_bits[i] = prepare_bit_vector(e[i],32);
		
        f_bits[i] = prepare_bit_vector(f[i],32);
		
        g_bits[i] = prepare_bit_vector(g[i],32);
		
        if(e_bits[i].size() != 32 || f_bits[i].size() != 32 || g_bits[i].size() != 32){
			printf("Error in witness 1\n");
			exit(-1);
		}
		w1 = rotate(e_bits[i],6);
		w2 = rotate(e_bits[i],11);
		w3 = rotate(e_bits[i],25);
		unsigned long long int s1 = 0;
		for(int j = 0; j < 32; j++){
			unsigned long long int _t = w1[j]+w2[j] - 2*w1[j]*w2[j];
			s1 = s1 + pow[j]*(w3[j] + _t - 2*w3[j]*_t);
		}
		unsigned long long int ch = (0);
		for(int j = 0; j < 32; j++){
			ch = ch+ pow[j]*(e_bits[i][j]*f_bits[i][j] + (1-e_bits[i][j])*g_bits[i][i] - 2*e_bits[i][j]*f_bits[i][j]* (1-e_bits[i][j])*g_bits[i][i]);
		}
		long long int t1 = ch + s1 + words[i] + h[i] + SHA[i];
		a_q.push_back((t1+t2)/(1ULL<<32));
		a[i+1] = (t1+t2)%((1ULL<<32));
		//printf("%lld , %lld\n",a_q[i].toint128()),(t1+t2 - a_q[i]*(1ULL<<32) - a[i+1]);
		e_q.push_back((t1 + d[i])/(1ULL<<32));
		e[i+1] = (t1 + d[i])%(1ULL<<32);
		h[i+1] = g[i];
		g[i+1] = f[i];
		f[i+1] = e[i];
		d[i+1] = c[i];
		c[i+1] = b[i];
		b[i+1] = a[i];
	}
	


	gkr_input.insert(gkr_input.end(),words.begin(),words.end());
	gkr_input.insert(gkr_input.end(),quotients.begin(),quotients.end());
	//gkr_input.insert(gkr_input.end(),pow.begin(),pow.end());
	
	for(int i = 0; i < a.size(); i++){
		gkr_input.push_back(a[i]);
		gkr_input.push_back(b[i]);
		gkr_input.push_back(c[i]);
		gkr_input.push_back(d[i]);
		gkr_input.push_back(e[i]);
		gkr_input.push_back(f[i]);
		gkr_input.push_back(g[i]);
		gkr_input.push_back(h[i]);
	}
	for(int i = 0; i < a_q.size(); i++){
		gkr_input.push_back(a_q[i]);
		gkr_input.push_back(e_q[i]);
	}
    for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),words_bits[i].begin(),words_bits[i].end());
	}

	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),a_bits[i].begin(),a_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),b_bits[i].begin(),b_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),c_bits[i].begin(),c_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),e_bits[i].begin(),e_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),f_bits[i].begin(),f_bits[i].end());
	}
	for(int i = 0; i < 64; i++){
		gkr_input.insert(gkr_input.end(),g_bits[i].begin(),g_bits[i].end());
	}
    gkr_input.push_back(1);
    F zero = F(0);
    gkr_input.resize(1ULL<<14,zero);
	//gkr_input.push_back(F(1));
	return gkr_input;
}



void reset_stream(stream_descriptor &fp){
    fp.pos = 0;
    fp.idx = 0;
    fp.stage = 0;
    fp.offset = 0;
    fp.finished = false;
}


void get_transcript(vector<vector<F>> &transcript){
    for(int i = 0; i < transcript.size(); i++){
        transcript[i].resize((1ULL << C.circuit[i].bitLength)*Circuits);
    }
    vector<F> buff;
    for(int z = 0; z < Circuits; z++){
        if(mod == 1 || mod == 3){
            F a = F(311322);
            for(int i = 0; i < transcript[0].size()/Circuits; i++){
                transcript[0][z*transcript[0].size()/Circuits + i] = a;
            }
        }else{
            buff = get_sha_witness(preimage);
            for(int i = 0; i < buff.size(); i++){
                transcript[0][z*buff.size() + i] = buff[i];
            }
        }
        for (u64 g = 0; g < C.circuit[0].size; ++g)
        {
            // make sure the gates are of type input
            auto info = C.circuit[0].gates[g];
            assert(info.ty == gateType::Input);
            //printf("%llu , %llu\n",g,C.circuit[0].gates[g].u );
            //printf("%llu\n",circuitValue[0][g].toint128());
        }
        //fclose(f);
        
        std::vector<std::pair<int, F> > ret;
        
        for (int i = 1; i < transcript.size(); ++i)
        {   
            for (u64 g = 0; g < C.circuit[i].size; ++g){
                // check info of each gate and compute the output
                auto info = C.circuit[i].gates[g];
                gateType ty = info.ty;
                int l = info.l;
                
                
                
                u64 u = info.u;
                u64 v = info.v;
                
                
                if(l != i-1){
                    printf("ERROR the circuit is not layered, %d %d\n",l,i);
                    exit(-1);
                }
                int counter = info.counter;
                F *x, *y;
                switch (ty) {
                    case gateType::Add:
                        transcript[i][z*transcript[i].size()/Circuits+ g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u] + transcript[l][z*transcript[l].size()/Circuits+v];
                    break;
                    case gateType::Sub:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u] - transcript[l][z*transcript[l].size()/Circuits+v];
                        break;
                    case gateType::Mul:
                        transcript[i][z*transcript[i].size()/Circuits+g] =  transcript[i - 1][z*transcript[i-1].size()/Circuits+u] * transcript[l][z*transcript[l].size()/Circuits+v];
                        break;
                    case gateType::AntiSub:
                        transcript[i][z*transcript[i].size()/Circuits+g] = -transcript[i - 1][z*transcript[i-1].size()/Circuits+u] + transcript[l][z*transcript[l].size()/Circuits+v];
                        break;
                    case gateType::AddMul:
                        transcript[i][z*transcript[i].size()/Circuits+g] = F(0);
                        for(int k = 0; k < counter; k++){
                            transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i][z*transcript[i].size()/Circuits+g] + transcript[i-1][z*transcript[i-1].size()/Circuits+info.vector_u.at(k)]*transcript[l][z*transcript[l].size()/Circuits+info.vector_v.at(k)];
                            //printf("%lld \n", circuitValue[i-1][info.vector_u.at(k)].toint128());
                        }
                        break;
                    case gateType::Naab:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[l][z*transcript[l].size()/Circuits+v] - transcript[i - 1][z*transcript[i-1].size()/Circuits+u] * transcript[l][z*transcript[l].size()/Circuits+v];
                    break;
                    case gateType::AntiNaab:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u] - transcript[i - 1][z*transcript[i-1].size()/Circuits+u] * transcript[l][z*transcript[l].size()/Circuits+v];
                    break;
                    case gateType::Addc:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u] + info.c;
                    break;
                    case gateType::Mulc:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u] * info.c;
                    break;
                    case gateType::Copy:
                        transcript[i][z*transcript[i].size()/Circuits+g] = transcript[i - 1][z*transcript[i-1].size()/Circuits+u];
                    break;
                    case gateType::Not:
                        transcript[i][z*transcript[i].size()/Circuits+g] = F_ONE - transcript[i - 1][z*transcript[i-1].size()/Circuits+u];
                    break;
                    case gateType::Xor:
                        x = &transcript[i - 1][z*transcript[i-1].size()/Circuits+u];
                        y = &transcript[l][z*transcript[l].size()/Circuits+v];
                        transcript[i][z*transcript[i].size()/Circuits+g] = *x + *y - F(2) * (*x) * (*y);
                    break;
                    default:
                        assert(false);
                }
            }
        }
    }
}


void read_layer(int circuit_num, int layer , vector<F> &V){
     if(C.size < layer){
        printf("Wrong layer \n");
        exit(-1);
    }
    
    vector<vector<F>> circuitValue; 
    circuitValue.resize(C.size + 1);
    //Change the size of the input layer
    if(mod == 1 || mod == 3){
        F a = F(311322);
        circuitValue[0].resize(1ULL << C.circuit[0].bitLength, F_ZERO);
        for(int i = 0; i < circuitValue[0].size(); i++){
           circuitValue[0][i] = a;
        }
    }else{
        circuitValue[0] = get_sha_witness(preimage);
    }
    
    for (u64 g = 0; g < C.circuit[0].size; ++g)
    {
        // make sure the gates are of type input
        auto info = C.circuit[0].gates[g];
        assert(info.ty == gateType::Input);
        //printf("%llu , %llu\n",g,C.circuit[0].gates[g].u );
        circuitValue[0][g] = (g+1)  + C.circuit[0].size*circuit_num;
        //printf("%llu\n",circuitValue[0][g].toint128());
    }
    if(layer == 0){
        for(int i = 0; i < circuitValue[0].size(); i++){
            V[i] = circuitValue[0][i];
        }
        return;
    }
    //fclose(f);
    
    std::vector<std::pair<int, F> > ret;
    
    for (int i = 1; i < layer+1; ++i)
    {   
        circuitValue[i].resize(C.circuit[i].size);
        for (u64 g = 0; g < C.circuit[i].size; ++g){
            // check info of each gate and compute the output
            auto info = C.circuit[i].gates[g];
            gateType ty = info.ty;
            int l = info.l;
            
            
            
            u64 u = info.u;
            u64 v = info.v;
            
            
            if(l != i-1){
                printf("ERROR the circuit is not layered, %d %d\n",l,i);
                exit(-1);
            }
            int counter = info.counter;
            F *x, *y;
            switch (ty) {
                case gateType::Add:
                    circuitValue[i][g] = circuitValue[i - 1][u] + circuitValue[l][v];
                break;
                case gateType::Sub:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[l][v];
                    break;
                case gateType::Mul:
                    circuitValue[i][g] =  circuitValue[i - 1][u] * circuitValue[l][v];
                    break;
                case gateType::AntiSub:
                    circuitValue[i][g] = -circuitValue[i - 1][u] + circuitValue[l][v];
                    break;
                case gateType::AddMul:
                    circuitValue[i][g] = F(0);
                    for(int k = 0; k < counter; k++){
                        circuitValue[i][g] = circuitValue[i][g] + circuitValue[i-1][info.vector_u.at(k)]*circuitValue[l][info.vector_v.at(k)];
                        //printf("%lld \n", circuitValue[i-1][info.vector_u.at(k)].toint128());
                    }
                    break;
                case gateType::Naab:
                    circuitValue[i][g] = circuitValue[l][v] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::AntiNaab:
                    circuitValue[i][g] = circuitValue[i - 1][u] - circuitValue[i - 1][u] * circuitValue[l][v];
                break;
                case gateType::Addc:
                    circuitValue[i][g] = circuitValue[i - 1][u] + info.c;
                break;
                case gateType::Mulc:
                    circuitValue[i][g] = circuitValue[i - 1][u] * info.c;
                break;
                case gateType::Copy:
                    circuitValue[i][g] = circuitValue[i - 1][u];
                break;
                case gateType::Not:
                    circuitValue[i][g] = F_ONE - circuitValue[i - 1][u];
                break;
                case gateType::Xor:
                    x = &circuitValue[i - 1][u];
                    y = &circuitValue[l][v];
                    circuitValue[i][g] = *x + *y - F(2) * (*x) * (*y);
                break;
                default:
                    assert(false);
            }
        }
    }

    for(int i = 0; i < circuitValue[layer].size(); i++){
        V[i] = circuitValue[layer][i];
    }
        
}

void compute_H( int layer , F *H_add,F *H_mul, F *V, int layer_size){
    for(int i = 0; i < layer_size; i++){
        H_add[i] = F_ZERO;
        H_mul[i] = F_ZERO;
    }
    int counter1 = 0;
    //printf("%d,%d\n",beta12.size(),beta11.size());
    #pragma omp parallel for
    for(int z = 0; z < Circuits; z++){
        for (u64 g = 0; g < C.circuit[layer].size; ++g) {
            // take each current gate 
            auto info = C.circuit[layer].gates[g];
            gateType ty = info.ty;
            int l = info.l;
            u64 u = info.u;
            u64 v = info.v;
            u64 lv = info.lv;
            int counter = info.counter;
            F tmp;
            if(a.size() == 0){
                tmp = beta11[g]*beta12[z];
            }else{
                tmp = a[0]*beta11[g]*beta12[z] + a[1]*beta13[g]*beta14[z];
            }
            //tmp *= beta_h2;
            switch (ty) {
                case gateType::Add:
                    
                    H_add[z*((layer_size/Circuits))+u] +=  V[z*(layer_size/Circuits)+v] * tmp; 
                    // That is add()V(i-1)(x)
                    H_mul[z*(layer_size/Circuits)+u] += tmp;
                    break;
                case gateType::Sub:
                    H_add[z*(layer_size/Circuits)+u] -=  V[z*(layer_size/Circuits)+v] * tmp;
                    H_mul[z*(layer_size/Circuits)+u] += tmp;
                    break;
                case gateType::Mul:
                    //printf("%d,%d\n",u,v);
                    H_mul[z*(layer_size/Circuits)+u] += V[z*(layer_size/Circuits)+v] * tmp;
                    break;
                case gateType::AntiSub:
                    H_add[z*(layer_size/Circuits)+u] = H_add[z*(layer_size/Circuits)+u] + V[z*(layer_size/Circuits)+v] * tmp;
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] - tmp;
                    break;
                case gateType::AddMul:
                    //tmp_mult[info.vector_u.at(0)] = F(0);
                    for(int k = 0; k < counter; k++){
                        H_mul[z*(layer_size/Circuits)+info.vector_u.at(k)] = H_mul[z*(layer_size/Circuits)+info.vector_u.at(k)]  + V[z*(layer_size/Circuits)+info.vector_v.at(k)]*tmp;
                    }
                    break;
                case gateType::Naab:
                    H_add[z*(layer_size/Circuits)+u] = H_add[z*(layer_size/Circuits)+u] + tmp * V[z*(layer_size/Circuits)+v];
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] - (V[z*(layer_size/Circuits)+v] * tmp);
                    break;
                case gateType::AntiNaab:
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] + (tmp - (V[z*(layer_size/Circuits)+v] * tmp));
                    break;
                case gateType::Addc:
                    H_add[z*(layer_size/Circuits)+u] = H_add[z*(layer_size/Circuits)+u] + info.c * tmp;
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] + tmp;
                    break;
                case gateType::Mulc:
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] + info.c * tmp;
                    break;
                case gateType::Copy:
                    H_mul[z*(layer_size/Circuits)+u] += tmp;
                    break;
                case gateType::Not:
                    H_add[z*(layer_size/Circuits)+u] = H_add[z*(layer_size/Circuits)+u] + tmp;
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] - tmp;
                    break;
                case gateType::Xor:
                    H_add[z*(layer_size/Circuits)+u] = H_add[z*(layer_size/Circuits)+u] + tmp * V[z*(layer_size/Circuits)+v];
                    H_mul[z*(layer_size/Circuits)+u] = H_mul[z*(layer_size/Circuits)+u] + tmp * (F_ONE - (V[z*(layer_size/Circuits)+v] + V[z*(layer_size/Circuits)+v]));
                    break;
                default:
                    assert(false);
            }
        }
    }
    
}

void read_H( int layer , vector<F> &H_add,vector<F> &H_mul, vector<F> &V, F beta_h1, F beta_h2 ){
    
    for(int i = 0; i < H_add.size(); i++){
        H_add[i] = F_ZERO;
        H_mul[i] = F_ZERO;
    }
    int counter1 = 0;
    for (u64 g = 0; g < C.circuit[layer].size; ++g) {
        // take each current gate 
        auto info = C.circuit[layer].gates[g];
        gateType ty = info.ty;
        int l = info.l;
        u64 u = info.u;
        u64 v = info.v;
        u64 lv = info.lv;
        int counter = info.counter;
        F tmp;
        if(a.size() == 0){
            tmp = beta11[g]*beta_h1;
        }else{
            tmp = a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2;
        }
        
        //tmp *= beta_h2;
        switch (ty) {
            case gateType::Add:
                
                H_add[u] +=  V[v] * tmp; 
                // That is add()V(i-1)(x)
                H_mul[u] += tmp;
                break;
            case gateType::Sub:
                H_add[u] -=  V[v] * tmp;
                H_mul[u] += tmp;
                break;
            case gateType::Mul:
                //printf("%d,%d\n",u,v);
                H_mul[u] += V[v] * tmp;
                break;
            case gateType::AntiSub:
                H_add[u] = H_add[u] + V[v] * tmp;
                H_mul[u] = H_mul[u] - tmp;
                break;
            case gateType::AddMul:
                //tmp_mult[info.vector_u.at(0)] = F(0);
                for(int k = 0; k < counter; k++){
                    H_mul[info.vector_u.at(k)] = H_mul[info.vector_u.at(k)]  + V[info.vector_v.at(k)]*tmp;
                }
                break;
            case gateType::Naab:
                H_add[u] = H_add[u] + tmp * V[v];
                H_mul[u] = H_mul[u] - (V[v] * tmp);
                break;
            case gateType::AntiNaab:
                H_mul[u] = H_mul[u] + (tmp - (V[v] * tmp));
                break;
            case gateType::Addc:
                H_add[u] = H_add[u] + info.c * tmp;
                H_mul[u] = H_mul[u] + tmp;
                break;
            case gateType::Mulc:
                H_mul[u] = H_mul[u] + info.c * tmp;
                break;
            case gateType::Copy:
                H_mul[u] += tmp;
                break;
            case gateType::Not:
                H_add[u] = H_add[u] + tmp;
                H_mul[u] = H_mul[u] - tmp;
                break;
            case gateType::Xor:
                H_add[u] = H_add[u] + tmp * V[v];
                H_mul[u] = H_mul[u] + tmp * (F_ONE - (V[v] + V[v]));
                break;
            default:
                assert(false);
        }
    }
}


void compute_G( int layer , F *G_add,F *G_mul, F *V, F *beta_g1,F V_u, int len){
    for(int i = 0; i < len; i++){
        G_add[i] = F_ZERO;
        G_mul[i] = F_ZERO;
    }
    #pragma omp parallel for
    for(int z = 0; z < Circuits; z++){
        for (u64 g = 0; g < C.circuit[layer].size; ++g)
        {
            auto info = C.circuit[layer].gates[g];
            gateType ty = info.ty;
            
            u64 u = info.u;
            u64 v = info.v;
            int counter = info.counter;
            // Create the bookkeeping table for the second phase
            // Note that this time tmp is not G[g], but G[g]*U[u]
            // Because add() and mul() contain x which has become 
            // u so there must be an identity function for x too
            F tmp;
            if(a.size() == 0){
                
                tmp = beta11[g]*beta12[z]*beta22[z]*beta_g1[u];
            }else{
                tmp = (a[0]*beta11[g]*beta12[z] + a[1]*beta13[g]*beta14[z])*beta22[z]*beta_g1[u];
            }
            
            //F tmp = beta_g1[u] * beta_h1[g]*beta_g2*beta_h2;
            
            //printf("%d,%d,%d\n",g,u,v);
            switch (ty) {
                case gateType::Add:
                    G_mul[z*(len/Circuits)+v] += tmp;
                    G_add[z*(len/Circuits)+v] += tmp * V_u;
                    break;
                case gateType::Sub:
                    G_add[z*(len/Circuits)+v] +=  tmp * V_u;
                    G_mul[z*(len/Circuits)+v] -=  tmp;
                    break;
                case gateType::Mul:
                    G_mul[z*(len/Circuits)+v] += tmp*V_u;
                    break;
                case gateType::AddMul:
                    //multArray[l][info.vector_lv.at(0)]= F(0);
                    for(int k = 0; k < counter; k++){
                        //printf("u : %d, v : %d\n", info.vector_u.at(k),info.vector_lv.at(k));
                        F tmp_add_mull;// = beta_g[g] * beta_u[info.vector_u.at(k)];
                        if(a.size() == 0){
                            tmp_add_mull = beta11[g]*beta12[z]*beta22[z]*beta_g1[info.vector_u.at(k)];
                        }else{
                            tmp_add_mull = (a[0]*beta11[g]*beta12[z] + a[1]*beta13[g]*beta14[z])*beta22[z]*beta_g1[info.vector_u.at(k)];
                        }
                        G_mul[z*(len/Circuits)+info.vector_v.at(k)] +=  tmp_add_mull*V_u ;
                    }
                    break;
                case gateType::Not:
                    G_add[z*(len/Circuits)+0] = G_add[z*(len/Circuits)+0] + tmp * (F_ONE - V_u);
                    break;
                case gateType::Xor:
                    
                    G_add[z*(len/Circuits)+v] = G_add[z*(len/Circuits)+v] + tmp * V_u;
                    G_mul[z*(len/Circuits)+v] = G_mul[z*(len/Circuits)+v] + tmp * (F_ONE - (V_u + V_u));
                    break;
                default:
                    assert(false);
            }
        }

    }
    
}



void read_G( int layer , vector<F> &G_add,vector<F> &G_mul, vector<F> &V, vector<F> &beta_g1,F beta_h1,
 F beta_g2,F beta_h2, F V_u){

     for(int i = 0; i < G_add.size(); i++){
        G_add[i] = F_ZERO;
        G_mul[i] = F_ZERO;
    }
     for (u64 g = 0; g < C.circuit[layer].size; ++g)
    {
        auto info = C.circuit[layer].gates[g];
        gateType ty = info.ty;
        
        u64 u = info.u;
        u64 v = info.v;
        int counter = info.counter;
        // Create the bookkeeping table for the second phase
        // Note that this time tmp is not G[g], but G[g]*U[u]
        // Because add() and mul() contain x which has become 
        // u so there must be an identity function for x too
        F tmp;
        if(a.size() == 0){
            tmp = beta11[g]*beta_h1*beta_g2*beta_g1[u];
        }else{
            tmp = (a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2)*beta_g2*beta_g1[u];
        }

        //F tmp = beta_g1[u] * beta_h1[g]*beta_g2*beta_h2;
        
        //printf("%d,%d,%d\n",g,u,v);
        switch (ty) {
            case gateType::Add:
                G_mul[v] += tmp;
                G_add[v] += tmp * V_u;
                break;
            case gateType::Sub:
                G_add[v] +=  tmp * V_u;
                G_mul[v] -=  tmp;
                break;
            case gateType::Mul:
                G_mul[v] += tmp*V_u;
                break;
            case gateType::AddMul:
                //multArray[l][info.vector_lv.at(0)]= F(0);
                for(int k = 0; k < counter; k++){
                    //printf("u : %d, v : %d\n", info.vector_u.at(k),info.vector_lv.at(k));
                    F tmp_add_mull;// = beta_g[g] * beta_u[info.vector_u.at(k)];
                    if(a.size() == 0){
                        tmp_add_mull = beta11[g]*beta_h1*beta_g2*beta_g1[info.vector_u.at(k)];
                    }else{
                        tmp_add_mull = (a[0]*beta11[g]*beta_h1 + a[1]*beta13[g]*beta_h2)*beta_g2*beta_g1[info.vector_u.at(k)];
                    }
                    G_mul[info.vector_v.at(k)] +=  tmp_add_mull*V_u ;
                }
                break;
            case gateType::Not:
                G_add[0] = G_add[0] + tmp * (F_ONE - V_u);
                break;
            case gateType::Xor:
                
                G_add[v] = G_add[v] + tmp * V_u;
                G_mul[v] = G_mul[v] + tmp * (F_ONE - (V_u + V_u));
                break;
            default:
                assert(false);
        }
    }

}

stream_descriptor tr_fd,mem_fd,lookup_fd;


int *addresses;
F *values;
int *accesses;
uint8_t *types; 
int ctr = 0;

int _read_witness(stream_descriptor &fd, vector<F> &buff_witness, int gates){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){
        if(gates == 0){
            if(fd.offset == 1){
                buff_witness[counter++] = tr[idx-1].value_r;
                buff_witness[counter++] = tr[idx-1].value_o;
            }else if(fd.offset == 2){
                buff_witness[counter++] = tr[idx-1].value_o;
            }
            fd.offset = 0;
            for(int i  = idx; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type > 0 && tr[i].type < 255){
                    buff_witness[counter] = tr[i].value_l;
                    counter++;
                    buff_witness[counter] = tr[i].value_r;
                    counter++;
                    buff_witness[counter] = tr[i].value_o;
                    counter++;

                }
                else if(tr[i].type == 255){
                    for(int  k =counter; k < buff_witness.size();k++){
                        buff_witness[k] = F(0);
                    }
                    return -1;
                }
            }
        }else{
            for(int i = idx; i < BUFFER_SPACE_tr; i++){
                if(!tr[i].type){
                    buff_witness[counter] = tr[i].value_o;
                    counter++;
                }
                else if(tr[i].type == 255){
                    for(int k = counter; k < buff_witness.size();k++){
                        buff_witness[k] = F(0);
                    }
                    return -1;
                }
            }
        }
    }
        
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            if(gates == 0){
                
                for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        for(int  k = counter; k < buff_witness.size();k++){
                            buff_witness[k] = F(0);
                        }
                        return -1;
                    }
                    else if(tr[i].type > 0){
                        if(counter + 3 <= buff_witness.size()){
                            buff_witness[counter++] = tr[i].value_l;
                            buff_witness[counter++] = tr[i].value_r;
                            buff_witness[counter++] = tr[i].value_o;
                        }else{
                            buff_witness[counter++] = tr[i].value_l;
                            if(counter == buff_witness.size()){
                                fd.idx = i+1;
                                fd.offset = 1;
                                return 1;
                            }
                            buff_witness[counter++] = tr[i].value_r;
                            if(counter == buff_witness.size()){
                                fd.idx = i+1;
                                fd.offset = 2;
                                return 1;
                            }
                        }
                    }
                    if(counter == buff_witness.size()){
                        fd.idx = i+1;
                        return 1;
                    }
                }
            }else{
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(!tr[i].type){
                        buff_witness[counter] = tr[i].value_o;
                        counter++;
                    }
                    else if(tr[i].type == 255){
                        for(int k = counter; k < buff_witness.size();k++){
                            buff_witness[k] = F(0);
                        }
                        return -1;
                    }
                    if(counter == buff_witness.size()){
                        fd.idx = i+1;
                        return 1;
                    }

                }
            }
        }
    
    return 1;   
}

int read_circuit_lookup(stream_descriptor &fd, vector<int> &buff){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){       
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type >= 3 && tr[i].type != 255){
                buff[counter++] = tr[i].type;
            }else if(tr[i].type == 1 || tr[i].type == 2){
                buff[counter++] = 0;
            }else if(tr[i].type == 255){
                for(int  k =counter; k < buff.size();k++){
                    buff[k] = 0;
                }
                return -1;
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type >= 3 && tr[i].type != 255){
                    buff[counter++] = tr[i].type;
                }else if(tr[i].type == 1 || tr[i].type == 2){
                    buff[counter++] = 0;
            }else if(tr[i].type == 255){
                    for(int  k =counter; k < buff.size();k++){
                        buff[k] = 0;
                    }
                    return -1;
                }
                if(counter == buff.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   

}

int read_lookup_transcript_basic(stream_descriptor &fd, vector<F> &buff){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){       
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type >= 3 && tr[i].type != 255){
                buff[counter++] = tr[i].value_l;
                buff[counter++] = tr[i].value_r;
                buff[counter++] = tr[i].value_o;
                // range proof table
                if(tr[i].type == 3){
                    buff[counter++] = access_table[0][tr[i].value_l.real];
                    access_table[0][tr[i].value_l.real]++;
                    buff[counter++] = tr[i].type;
                }else{
                    buff[counter++] = access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real];
                    access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real]++;
                    buff[counter++] = tr[i].type;
                }
            }else if(tr[i].type == 1 || tr[i].type == 2){
                buff[counter++] = 0;
                buff[counter++] = 0;
                buff[counter++] = 0;
                buff[counter++] = 0;
                buff[counter++] = 0;
            }else if(tr[i].type == 255){
                for(int  k =counter; k < buff.size();k++){
                    buff[k] = F(0);
                }
                return -1;
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type >= 3 && tr[i].type != 255){
                    buff[counter++] = tr[i].value_l;
                    buff[counter++] = tr[i].value_r;
                    buff[counter++] = tr[i].value_o;
                    // range proof table
                    if(tr[i].type == 3){
                        buff[counter++] = access_table[0][tr[i].value_l.real];
                        access_table[0][tr[i].value_l.real]++;
                        buff[counter++] = tr[i].type;
                    }else{
                        buff[counter++] = access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real];
                        access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real]++;
                        buff[counter++] = tr[i].type;
                    }
                }else if(tr[i].type == 1 || tr[i].type == 2){
                    buff[counter++] = 0;
                    buff[counter++] = 0;
                    buff[counter++] = 0;
                    buff[counter++] = 0;
                    buff[counter++] = 0;
            }   else if(tr[i].type == 255){
                    for(int  k =counter; k < buff.size();k++){
                        buff[k] = F(0);
                    }
                    return -1;
                }
                if(counter == buff.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   

}

int read_lookup_transcript(stream_descriptor &fd, vector<F> &buff){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){       
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type >= 3 && tr[i].type != 255){
                buff[counter++] = tr[i].value_o;
                buff[counter++] = tr[i].value_l;
                buff[counter++] = tr[i].value_r;
                // range proof table
                if(tr[i].type == 3){
                    buff[counter++] = access_table[0][tr[i].value_l.real];
                    access_table[0][tr[i].value_l.real]++;
                    buff[counter++] = tr[i].type;
                }else{
                    buff[counter++] = access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real];
                    access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real]++;
                    buff[counter++] = tr[i].type;
                }
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type >= 3 && tr[i].type != 255){
                    buff[counter++] = tr[i].value_o;
                    buff[counter++] = tr[i].value_l;
                    buff[counter++] = tr[i].value_r;
                    // range proof table
                    if(tr[i].type == 3){
                        buff[counter++] = access_table[0][tr[i].value_l.real];
                        access_table[0][tr[i].value_l.real]++;
                        buff[counter++] = tr[i].type;
                    }else{
                        buff[counter++] = access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real];
                        access_table[tr[i].type-3][tr[i].value_l.real+256*tr[i].value_r.real]++;
                        buff[counter++] = tr[i].type;
                    }
                }else if(tr[i].type == 255){
                    for(int  k =counter; k < buff.size();k++){
                        buff[k] = F(0);
                    }
                    return -1;
                }
                if(counter == buff.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   

}

int read_memory_trancript(stream_descriptor &fd, vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f, int write){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){
        if(fd.offset == 1){
                buff_addr[counter] = tr[idx-1].idx_r;// addresses[i];
                buff_v[counter] = tr[idx-1].value_r;// values[i];
                buff_f[counter++] = tr[idx-1].access_r+write;// (accesses[i]+write);
                buff_addr[counter] = tr[idx-1].idx_o;// addresses[i];
                buff_v[counter] = tr[idx-1].value_o;// values[i];
                buff_f[counter++] = tr[idx-1].access_o+write;// (accesses[i]+write);
        
        }else if(fd.offset == 2){
                buff_addr[counter] = tr[idx-1].idx_o;// addresses[i];
                buff_v[counter] = tr[idx-1].value_o;// values[i];
                buff_f[counter++] = tr[idx-1].access_o+write;// (accesses[i]+write);
       
        }
        fd.offset = 0;
            
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type > 0 && tr[i].type != 255){
                buff_addr[counter] = tr[i].idx_l;// addresses[i];
                buff_v[counter] =tr[i].value_l;// values[i];
                buff_f[counter++] = tr[i].access_l +write;// (accesses[i]+write);
                buff_addr[counter] = tr[i].idx_r;// addresses[i];
                buff_v[counter] = tr[i].value_r;// values[i];
                buff_f[counter++] = tr[i].access_r+write;// (accesses[i]+write);
                buff_addr[counter] = tr[i].idx_o;// addresses[i];
                buff_v[counter] = tr[i].value_o;// values[i];
                buff_f[counter++] = tr[i].access_o+write;// (accesses[i]+write);
            }else if(tr[i].type == 255){
                for(int j = counter; j < buff_addr.size(); j++){
                    buff_addr[j] = F(0);
                    buff_v[j] = F(0);
                    buff_f[j] = F(0);
                }
                return -1;
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type > 0 && tr[i].type != 255){
                    if(counter + 3 <= buff_addr.size()){
                        buff_addr[counter] = tr[i].idx_l;// addresses[i];
                        buff_v[counter] =tr[i].value_l;// values[i];
                        buff_f[counter++] = tr[i].access_l +write;// (accesses[i]+write);
                        buff_addr[counter] = tr[i].idx_r;// addresses[i];
                        buff_v[counter] = tr[i].value_r;// values[i];
                        buff_f[counter++] = tr[i].access_r+write;// (accesses[i]+write);
                        buff_addr[counter] = tr[i].idx_o;// addresses[i];
                        buff_v[counter] = tr[i].value_o;// values[i];
                        buff_f[counter++] = tr[i].access_o+write;// (accesses[i]+write);
                
                    }else{
                        buff_addr[counter] = tr[i].idx_l;// addresses[i];
                        buff_v[counter] =tr[i].value_l;// values[i];
                        buff_f[counter++] = tr[i].access_l +write;// (accesses[i]+write);
                        
                        if(counter == buff_addr.size()){
                            fd.idx = i+1;
                            fd.offset = 1;
                            return 1;
                        }
                        buff_addr[counter] = tr[i].idx_r;// addresses[i];
                        buff_v[counter] = tr[i].value_r;// values[i];
                        buff_f[counter++] = tr[i].access_r+write;// (accesses[i]+write);
                      
                        if(counter == buff_addr.size()){
                            fd.idx = i+1;
                            fd.offset = 2;
                            return 1;
                        }
                    }
                }else if(tr[i].type == 255){
                        for(int  k =counter; k < buff_addr.size();k++){
                            buff_addr[k] = F(0);
                            buff_v[k] = F(0);
                            buff_f[k] = F(0);
                        }
                        return -1;
                }
                if(counter == buff_addr.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   
}

int read_memory_trancript_alt(stream_descriptor &fd, vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f, int write){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){
        fd.offset = 0;
            
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type > 0 && tr[i].type != 255){
                buff_addr[counter] = tr[i].idx_l;// addresses[i];
                buff_v[counter] =tr[i].value_l;// values[i];
                buff_f[counter++] = tr[i].access_l +write;// (accesses[i]+write);
            }else if(tr[i].type == 255){
                for(int j = counter; j < buff_addr.size(); j++){
                    buff_addr[j] = F(0);
                    buff_v[j] = F(0);
                    buff_f[j] = F(0);
                }
                return -1;
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type > 0 && tr[i].type != 255){
                        buff_addr[counter] = tr[i].idx_l;// addresses[i];
                        buff_v[counter] =tr[i].value_l;// values[i];
                        buff_f[counter++] = tr[i].access_l +write;// (accesses[i]+write);                
                    
                }else if(tr[i].type == 255){
                        for(int  k =counter; k < buff_addr.size();k++){
                            buff_addr[k] = F(0);
                            buff_v[k] = F(0);
                            buff_f[k] = F(0);
                        }
                        return -1;
                }
                if(counter == buff_addr.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   
}

int read_final_memory_trancript(stream_descriptor &fd, vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f, int write){
    int counter = 0;
    int idx = fd.idx;
   
    if(idx != 0){
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 0){
                buff_addr[counter] = tr[i].idx_o;
                buff_v[counter] = tr[i].value_o;
                if(write == 0){
                    buff_f[counter] = F(0);
                }else{
                    buff_f[counter] = (tr[i].access_o);
                }
                counter++;
            }else if(tr[i].type == 255){
                for(int  k =counter; k < buff_addr.size();k++){
                    buff_addr[k] = F(0);
                    buff_v[k] = F(0);
                    buff_f[k] = F(0);
                }
                return -1;
            }
        }
    }
    fd.idx = 0;
    while(true){
        mtx.unlock();
        mtx2.lock();
        
        for(int i  = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 0){
                buff_addr[counter] = tr[i].idx_o;
                buff_v[counter] = tr[i].value_o;
                if(write == 0){
                    buff_f[counter] = F(0);
                }else{
                    buff_f[counter] = (tr[i].access_o);
                }
                counter++;
            }else if(tr[i].type == 255){
                for(int k = counter; k < buff_addr.size();k++){
                    buff_addr[k] = F(0);
                    buff_v[k] = F(0);
                    buff_f[k] = F(0);
                }
                return -1;
            }
            if(counter == buff_addr.size()){
                fd.idx = i+1;
                return 1;
            }
        }
    }
      
    return 1;   
}

void read_witness(stream_descriptor &fd,  vector<F> &buff_witness){
    if((fd.stage == 0) && fd.pos == (3*ops/buff_witness.size())){
        //printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }
        //printf("New stage\n");
        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.pos = 0;
        fd.idx = 0;
        fd.offset=0;
    }
    if(fd.stage == 0){
        if(!fd.finished){
            if(_read_witness(fd,buff_witness,fd.stage) == -1){
                fd.finished = true;
            }
        }else{
            for(int i = 0; i  < buff_witness.size(); i++){
                buff_witness[i] = F(0);
            }
        }
        fd.pos++;
    }else{
        if(!fd.finished){
            if(_read_witness(fd,buff_witness,fd.stage) == -1){
                fd.finished = true;
            }
        }else{
            for(int i = 0; i  < buff_witness.size(); i++){
                buff_witness[i] = F(0);
            }
        }
        fd.pos++;
    }
    if(fd.stage == 1 && fd.pos == gates/buff_witness.size()){
        //printf("Finishing %d\n",fd.stage);
        
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
            //while(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) != -1){
            //}
        }
        //printf(">New stage\n");
        
        fd.stage = 0;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.idx = 0;

        //printf("Stage : %d\n", fd.stage%4);
        fd.pos = 0;
    
    }
}

void read_memory(stream_descriptor &fd,  vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f){
    //printf("%d,%d\n",fd.pos , circuit_size/buff_addr.size());
    if((fd.stage == 1 || fd.stage == 0) && fd.pos == (3*ops/buff_addr.size())){
        //printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }
        fd.stage += 1;
        fd.stage = fd.stage%4;
        fd.finished = false;
        fd.pos = 0;
        fd.idx = 0;
    }else if((fd.stage == 2) && fd.pos == gates/buff_addr.size()){
       //printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }
        fd.stage += 1;
        fd.stage = fd.stage%4;
        fd.finished = false;
        fd.idx = 0;
        fd.pos = 0;
    }
    if(fd.stage == 0 || fd.stage == 1){
        if(!fd.finished){
            if(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) == -1){
                fd.finished = true;
            }
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }else{
        if(!fd.finished){
            if(read_final_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage-2) == -1){
                fd.finished = true;
            }
            //printf("%d\n",ctr);
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }
    if(fd.stage == 3 && fd.pos == gates/buff_addr.size()){
        //printf("Finishing %d\n",fd.stage);
        
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
            //while(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) != -1){
            //}
        }
        fd.stage += 1;
        fd.stage = fd.stage%4;
        fd.finished = false;
        fd.idx = 0;

        //printf("Stage : %d\n", fd.stage%4);
        fd.pos = 0;
    }
    
}

void read_lookups_circuit(stream_descriptor &fd, vector<int> &buff){
   
    if(!fd.finished){
        if(read_circuit_lookup(fd,buff) == -1){
            fd.finished = true;
        }
    }else{
        for(int i = 0; i  < buff.size(); i++){
            buff[i] = 0;
        }
    }
    fd.pos++;
     if(fd.pos == fd.size/buff.size()){
        while(true){
            bool flag = false;
            for(int i = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type == 255){
                    flag = true;
                    break;
                }
            }
            if(flag) break;
            mtx.unlock();
            mtx2.lock();
        }
        fd.pos = 0;
        fd.finished = false;
    }
}

void read_lookups_basic(stream_descriptor &fd, vector<F> &buff){
   
    if(!fd.finished){
        if(read_lookup_transcript_basic(fd,buff) == -1){
            fd.finished = true;
        }
    }else{
        for(int i = 0; i  < buff.size(); i++){
            buff[i] = F(0);
        }
    }
    fd.pos++;
     if(fd.pos == 5*fd.size/buff.size()){
        while(true){
            bool flag = false;
            for(int i = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type == 255){
                    flag = true;
                    break;
                }
            }
            if(flag) break;
            mtx.unlock();
            mtx2.lock();
        }
        fd.pos = 0;
        fd.finished = false;
    }
}

void read_lookups(stream_descriptor &fd, vector<F> &buff){
   
    if(!fd.finished){
        if(read_lookup_transcript(fd,buff) == -1){
            fd.finished = true;
        }
    }else{
        for(int i = 0; i  < buff.size(); i++){
            buff[i] = F(0);
        }
    }
    fd.pos++;
     if(fd.pos == 5*fd.size/buff.size()){
        while(true){
            bool flag = false;
            for(int i = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type == 255){
                    flag = true;
                    break;
                }
            }
            if(flag) break;
            mtx.unlock();
            mtx2.lock();
        }
        fd.pos = 0;
        fd.finished = false;
    }
}

void read_memory_alt(stream_descriptor &fd,  vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f){
    if((fd.stage == 2) && fd.pos == (3*ops/buff_addr.size())){
        printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }

        fd.stage += 1;
        //fd.stage = fd.stage%2;
        fd.finished = false;
        fd.pos = 0;
        fd.idx = 0;
    }
    if(fd.stage < 3){
        //printf("%d,%d\n",fd.pos,3*ops/buff_addr.size());
        if(!fd.finished){
            if(read_memory_trancript_alt(fd,buff_addr,buff_v,buff_f,fd.stage) == -1){
                printf("OK\n");
                if(fd.stage == 2){
                    fd.finished = true;
                }else{
                    fd.stage++;
                    mtx.unlock();
                    mtx2.lock();
                }
            }
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }else{
        if(!fd.finished){
            if(read_final_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) == -1){
                fd.finished = true;
            }
            //printf("%d\n",ctr);
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }
    if(fd.stage == 3 && fd.pos == gates/buff_addr.size()){
        //printf("OK\n");
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
            //while(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) != -1){
            //}
        }
        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.idx = 0;
        fd.pos = 0;
    
    }
}

void read_memory_opt(stream_descriptor &fd,  vector<F> &buff_addr, vector<F> &buff_v, vector<F> &buff_f){
    
    if((fd.stage == 0) && fd.pos == (3*ops/buff_addr.size())){
        //printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }

        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.pos = 0;
        fd.idx = 0;
    }
    if(fd.stage == 0){
        if(!fd.finished){
            if(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) == -1){
                fd.finished = true;
            }
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }else{
        if(!fd.finished){
            if(read_final_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) == -1){
                fd.finished = true;
            }
            //printf("%d\n",ctr);
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_v[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }
    if(fd.stage == 1 && fd.pos == gates/buff_addr.size()){
        //printf("OK\n");
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
            //while(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) != -1){
            //}
        }
        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.idx = 0;
        fd.pos = 0;
    
    }
}


void read_trace(stream_descriptor &fd, vector<F> &buff_L,vector<F> &buff_R,vector<F> &buff_O,
    vector<int> &buff_S){
    
    int counter = 0;
    int idx = fd.idx;
    if(fd.finished == true){
        if(fd.pos == fd.size/buff_L.size()){
            fd.finished = false;
            fd.pos = 0;
            fd.idx = 0;
        }else{
            for(int  k =counter; k < buff_L.size();k++){
                buff_L[k] = F(0);
                buff_R[k] = F(0);
                buff_O[k] = F(0);
                buff_S[k] = 0;
            }
            fd.pos++;
            return;
        }
    }
    if(idx != 0){
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 1){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                if(has_lookups){
                    buff_S[counter++] = 0;
                }else{
                    buff_S[counter++] = 1;
               }
            }else if(tr[i].type == 2){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                if(has_lookups){
                    buff_S[counter++] = 1;
                }else{
                    buff_S[counter++] = 0;
                }
            }else if(tr[i].type > 2 && tr[i].type < 255){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                buff_S[counter++] = 2;
            }else if(tr[i].type == 255){
                fd.finished = true;
                for(int  k =counter; k < buff_L.size();k++){
                    buff_L[k] = F(0);
                    buff_R[k] = F(0);
                    buff_O[k] = F(0);
                    buff_S[k] = 0;
                }
                fd.pos++;
                return;
            }
        }
    }
    while(true){
        mtx.unlock();
        mtx2.lock();
      
        for(int i = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 1){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                if(has_lookups){
                    buff_S[counter++] = 0;
                }else{
                    buff_S[counter++] = 1;
               }
            }else if(tr[i].type == 2){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                if(has_lookups){
                    buff_S[counter++] = 1;
                }else{
                    buff_S[counter++] = 0;
                }
            }else if(tr[i].type > 2 && tr[i].type < 255){
                buff_L[counter] = tr[i].value_l;
                buff_R[counter] = tr[i].value_r;
                buff_O[counter] = tr[i].value_o;
                buff_S[counter++] = 2;
            }else if(tr[i].type == 255){
                fd.finished = true;
                for(int  k =counter; k < buff_L.size();k++){
                    buff_L[k] = F(0);
                    buff_R[k] = F(0);
                    buff_O[k] = F(0);
                    buff_S[k] = 0;
                }
                fd.pos++;
                return;
            }
            if(counter == buff_L.size()){
                fd.idx = i+1;
                fd.pos++;
                return;
            }
        }
    }

}

vector<F> addr,value,freq;
extern F a_w,b_w;

int read_circuit_memory_transcript(stream_descriptor &fd,  vector<F> &buff_addr,vector<F> &buff_f){
    int counter = 0;
    int idx = fd.idx;
    if(idx != 0){
        if(fd.offset == 1){
                buff_addr[counter] = tr[idx-1].idx_r;// addresses[i];
                buff_f[counter++] = tr[idx-1].access_r;// (accesses[i]+write);
                buff_addr[counter] = tr[idx-1].idx_o;// addresses[i];
                buff_f[counter++] = tr[idx-1].access_o;// (accesses[i]+write);
        
        }else if(fd.offset == 2){
                buff_addr[counter] = tr[idx-1].idx_o;// addresses[i];
                buff_f[counter++] = tr[idx-1].access_o;// (accesses[i]+write);
       
        }
        fd.offset = 0;
            
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type > 0 && tr[i].type != 255){
                buff_addr[counter] = tr[i].idx_l;// addresses[i];
                buff_f[counter++] = tr[i].access_l;// (accesses[i]+write);
                buff_addr[counter] = tr[i].idx_r;// addresses[i];
                buff_f[counter++] = tr[i].access_r;// (accesses[i]+write);
                buff_addr[counter] = tr[i].idx_o;// addresses[i];
                buff_f[counter++] = tr[i].access_o;// (accesses[i]+write);
            }else if(tr[i].type == 255){
                for(int j = counter; j < buff_addr.size(); j++){
                    buff_addr[j] = F(0);
                    buff_f[j] = F(0);
                }
                return -1;
            }
        }
    }
        fd.idx = 0;
        while(true){
            mtx.unlock();
            mtx2.lock();
            bool flag = false;
            for(int i  = 0; i < BUFFER_SPACE_tr; i++){
                if(tr[i].type > 0 && tr[i].type != 255){
                    if(counter + 3 <= buff_addr.size()){
                        buff_addr[counter] = tr[i].idx_l;// addresses[i];
                        buff_f[counter++] = tr[i].access_l;// (accesses[i]+write);
                        buff_addr[counter] = tr[i].idx_r;// addresses[i];
                        buff_f[counter++] = tr[i].access_r;// (accesses[i]+write);
                        buff_addr[counter] = tr[i].idx_o;// addresses[i];
                        buff_f[counter++] = tr[i].access_o;// (accesses[i]+write);
                
                    }else{
                        buff_addr[counter] = tr[i].idx_l;// addresses[i];
                        buff_f[counter++] = tr[i].access_l;// (accesses[i]+write);
                        
                        if(counter == buff_addr.size()){
                            fd.idx = i+1;
                            fd.offset = 1;
                            return 1;
                        }
                        buff_addr[counter] = tr[i].idx_r;// addresses[i];
                        buff_f[counter++] = tr[i].access_r;// (accesses[i]+write);
                      
                        if(counter == buff_addr.size()){
                            fd.idx = i+1;
                            fd.offset = 2;
                            return 1;
                        }
                    }
                }else if(tr[i].type == 255){
                        for(int  k =counter; k < buff_addr.size();k++){
                            buff_addr[k] = F(0);
                            buff_f[k] = F(0);
                        }
                        return -1;
                }
                if(counter == buff_addr.size()){
                    fd.idx = i+1;
                    return 1;
                }
            }
        }
    
    return 1;   
}

int read_circuit_memory_final(stream_descriptor &fd,  vector<F> &buff_addr,vector<F> &buff_f){
    int counter = 0;
    int idx = fd.idx;
   
    if(idx != 0){
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 0){
                buff_addr[counter] = tr[i].idx_o;
                buff_f[counter] = (tr[i].access_o);                
                counter++;
            }else if(tr[i].type == 255){
                for(int  k =counter; k < buff_addr.size();k++){
                    buff_addr[k] = F(0);
                    buff_f[k] = F(0);
                }
                return -1;
            }
        }
    }
    fd.idx = 0;
    while(true){
        mtx.unlock();
        mtx2.lock();
        
        for(int i  = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 0){
                buff_addr[counter] = tr[i].idx_o;
                buff_f[counter] = (tr[i].access_o);
                counter++;
            }else if(tr[i].type == 255){
                for(int k = counter; k < buff_addr.size();k++){
                    buff_addr[k] = F(0);
                    buff_f[k] = F(0);
                }
                return -1;
            }
            if(counter == buff_addr.size()){
                fd.idx = i+1;
                return 1;
            }
        }
    }
    return 1;   
}


int read_memory_circuit(stream_descriptor &fd,  vector<F> &buff_addr, vector<F> &buff_f){
    
    if((fd.stage == 0) && fd.pos == (3*ops/buff_addr.size())){
        //printf("New stage %d\n",fd.stage);
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
        }

        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.pos = 0;
        fd.idx = 0;
    }
    if(fd.stage == 0){
        if(!fd.finished){
            if(read_circuit_memory_transcript(fd,buff_addr,buff_f) == -1){
                fd.finished = true;
            }
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }else{
        if(!fd.finished){
            if(read_circuit_memory_final(fd,buff_addr,buff_f) == -1){
                fd.finished = true;
            }
            //printf("%d\n",ctr);
        }else{
            for(int i = 0; i  < buff_addr.size(); i++){
                buff_addr[i] = F(0);
                buff_f[i] = F(0);
            }
        }
        fd.pos++;
    }
    if(fd.stage == 1 && fd.pos == gates/buff_addr.size()){
        if(!fd.finished){
            while(true){
                bool flag = false;
                for(int i = 0; i < BUFFER_SPACE_tr; i++){
                    if(tr[i].type == 255){
                        flag = true;
                        break;
                    }
                }
                if(flag) break;
                mtx.unlock();
                mtx2.lock();
            }
            //while(read_memory_trancript(fd,buff_addr,buff_v,buff_f,fd.stage) != -1){
            //}
        }
        fd.stage += 1;
        fd.stage = fd.stage%2;
        fd.finished = false;
        fd.idx = 0;
        fd.pos = 0;
    
    }
}



void read_circuit_trace(stream_descriptor &fd,  vector<int> &buff){
    int counter = 0;
    int idx = fd.idx;
    if(fd.finished == true){
        if(fd.pos == fd.size/buff.size()){
            fd.finished = false;
            fd.pos = 0;
            fd.idx = 0;
        }else{
            for(int  k =counter; k < buff.size();k++){
                buff[k] = 0;
            }
            fd.pos++;
            return;
        }
    }
    if(idx != 0){
        for(int i  = idx; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 1){
                if(has_lookups){
                    buff[counter++] = 0;
                    buff[counter++] = 0;
                }else{
                    buff[counter++] = 1;
               }
            }else if(tr[i].type == 2){
                if(has_lookups){
                    buff[counter++] = 1;
                    buff[counter++] = 0;
                }else{
                    buff[counter++] = 0;
                }
            }else if(tr[i].type > 2 && tr[i].type < 255){
                buff[counter++] = 0;
                buff[counter++] = 1;
            }else if(tr[i].type == 255){
                fd.finished = true;
                for(int  k =counter; k < buff.size();k++){
                    buff[k] = 0;
                }
                fd.pos++;
                return;
            }
        }
    }
    while(true){
        mtx.unlock();
        mtx2.lock();
      
        for(int i = 0; i < BUFFER_SPACE_tr; i++){
            if(tr[i].type == 1){
                if(has_lookups){
                    buff[counter++] = 0;
                    buff[counter++] = 0;
                }else{
                    buff[counter++] = 1;
               }
            }else if(tr[i].type == 2){
                if(has_lookups){
                    buff[counter++] = 1;
                    buff[counter++] = 0;                    
                }else{
                    buff[counter++] = 0;
                }
            }else if(tr[i].type > 2 && tr[i].type < 255){
                buff[counter++] = 0;                    
                buff[counter++] = 1;
            }else if(tr[i].type == 255){
                fd.finished = true;
                for(int  k =counter; k < buff.size();k++){
                    buff[k] = 0;
                }
                fd.pos++;
                return;
            }
            if(counter == buff.size()){
                fd.idx = i+1;
                fd.pos++;
                return;
            }
        }
    }
}


void read_stream(stream_descriptor &fd, vector<F> &v, int size){
    
    if(fd.name == "input"){
        if(mod == 1 || mod == 3){
            for(int i =0 ; i < size; i++){
                v[i] = F(i%1024);
            }
        }else{
            vector<F> buff;
            int counter = 0;
            for(int i = 0; i < size/C.circuit[0].size; i++){
                buff = get_sha_witness(preimage);
                for(int j = 0; j < buff.size(); j++){
                    v[counter++] = buff[j];
                }
            }
        }
    }else if(fd.name == "circuit"){
        if(fd.pos == 0){
            tr_fd.size = circuit_size;
            if(has_lookups){
                tr_fd.size = 2*tr_fd.size;
            }
            lookup_fd.size = circuit_size;
            mem_fd.size = 4*circuit_size; 
            reset_stream(mem_fd);
            reset_stream(tr_fd);
            reset_stream(lookup_fd);
        }
        if(tr_fd.pos < tr_fd.size/size){
            vector<int> buff_S(size);
            read_circuit_trace(tr_fd,  buff_S);
            for(int i = 0; i < size; i++){
                v[i] = buff_S[i];
            }
            fd.pos++;
        }else if((!has_lookups && fd.pos < 9*circuit_size/size)||(has_lookups && fd.pos < 10*circuit_size/size)){
            vector<F> buff_addr(size/2),buff_f(size/2);
            read_memory_circuit(mem_fd,buff_addr,buff_f);
            for(int i = 0; i < size/2; i++){
                v[2*i] = buff_addr[i];
                v[2*i+1] = buff_f[i];
            }
            fd.pos++;
        }else if(has_lookups && fd.pos < 11*circuit_size/size){
            //printf("%d,\n",fd.pos);
            vector<int> buff_type(size);
            read_lookups_circuit(lookup_fd,buff_type);
            for(int i = 0; i < size; i++){
                v[i] = buff_type[i];
            }
            fd.pos++;
        }else{
            for(int i = 0; i < size; i++){
                v[i] = F(0);    
            }
        }
    }else if(fd.name == "witness"){
        if(addr.size() == 0){
            addr.resize(size);
            value.resize(size);
            freq.resize(size);
            addresses = new int[3*BUFFER_SPACE_tr];
            values = new F[3*BUFFER_SPACE_tr];
            accesses = new int[3*BUFFER_SPACE_tr];
            types = new uint8_t[3*BUFFER_SPACE_tr];
        }
        if(addr.size() != size){
            addr.resize(size,F(0));
            value.resize(size);
            freq.resize(size);
        }
        read_witness(fd,v);
    }else if(fd.name == "wiring_consistency_check"){
        if(addr.size() == 0){
            addr.resize(size);
            value.resize(size);
            freq.resize(size);
            addresses = new int[3*BUFFER_SPACE_tr];
            values = new F[3*BUFFER_SPACE_tr];
            accesses = new int[3*BUFFER_SPACE_tr];
            types = new uint8_t[3*BUFFER_SPACE_tr];
        }
        if(addr.size() != size){
            addr.resize(size,F(0));
            value.resize(size);
            freq.resize(size);
        }
        read_memory(fd,addr,value,freq);
        for(int i = 0; i < addr.size(); i++){
            v[i] = addr[i]+F(1)+a_w*value[i] + b_w*freq[i];
        }
    }else if(fd.name == "lookup_basic"){
        if(access_table.size() == 0){
            access_table.resize(lookup_table.size());
            for(int  i = 0; i < lookup_table.size(); i++){
                access_table[i].resize(lookup_table[i].size(),0);
            }
        }
        if(fd.pos == 0){
            for(int i = 0; i < access_table.size(); i++){
                for(int j = 0; j < access_table[i].size(); j++){
                    access_table[i][j] = 0;
                }
            }
        }
        vector<F> buff(5*size/2);
        read_lookups_basic(fd,buff);
        for(int i  = 0; i < buff.size()/5; i++){
            v[i] = F(1)+ buff[5*i];
            for(int j = 1; j < 5; j++){
                v[i] += lookup_rand[j-1]*buff[5*i + j];
            }
            if(v[i] == F(1)){
                v[i+size/2] = F(1);
            }else{
                v[i+size/2] = v[i] + lookup_rand[2];
            }
        }
    }else if(fd.name == "lookup_witness_basic"){
        if(access_table.size() == 0){
            access_table.resize(lookup_table.size());
            for(int  i = 0; i < lookup_table.size(); i++){
                access_table[i].resize(lookup_table[i].size(),0);
            }
        }
        if(fd.pos == 0){
            for(int i = 0; i < access_table.size(); i++){
                for(int j = 0; j < access_table[i].size(); j++){
                    access_table[i][j] = 0;
                }
            }
        }
        vector<F> buff(5*size/2);
        read_lookups(fd,buff);
        for(int i  = 0; i < buff.size()/5; i++){
            v[2*i] = buff[5*i];
            for(int j = 1; j < 3; j++){
                v[2*i] += lookup_rand[j-1]*buff[5*i + j];
            }
            v[2*i+1] = buff[5*i + 3];
        }
    }else if(fd.name == "lookup_check"){
        if(access_table.size() == 0){
            access_table.resize(lookup_table.size());
            for(int  i = 0; i < lookup_table.size(); i++){
                access_table[i].resize(lookup_table[i].size(),0);
            }
        }
        if(fd.pos == 0){
            for(int i = 0; i < access_table.size(); i++){
                for(int j = 0; j < access_table[i].size(); j++){
                    access_table[i][j] = 0;
                }
            }
        }
        vector<F> buff(5*size/2);
        read_lookups(fd,buff);
        for(int i  = 0; i < buff.size()/5; i++){
            v[i] = F(1)+ buff[5*i];
            for(int j = 1; j < 5; j++){
                v[i] += lookup_rand[j-1]*buff[5*i + j];
            }
            if(v[i] == F(1)){
                v[i+size/2] = F(1);
            }else{
                v[i+size/2] = v[i] + lookup_rand[2];
            }
        }
    }
    else if(fd.name == "wiring_consistency_check_opt"){
        if(addr.size() == 0){
            addr.resize(size/2);
            value.resize(size/2);
            freq.resize(size/2);
        }
        if(addr.size() != size/2){
            addr.resize(size/2,F(0));
            value.resize(size/2);
            freq.resize(size/2);
        }
       
        read_memory_opt(fd,addr,value,freq);
       
        if(fd.stage == 0 && fd.pos != 0){
            for(int i = 0; i < addr.size(); i++){
                v[i] = addr[i]+F(1)+a_w*value[i] + b_w*freq[i];
            }
            int offset = addr.size();
            for(int i = 0; i < addr.size(); i++){
                if(v[i] == F(1)){
                    v[i+offset] = v[i];    
                }else{
                    v[i+offset] = v[i]+b_w;
                }
            }
        }else{
            for(int i = 0; i < addr.size(); i++){
                v[i] = addr[i]+F(1)+a_w*value[i];// + b_w*freq[i];
            }
            int offset = addr.size();
            for(int i = 0; i < addr.size(); i++){
                v[i+offset] = v[i]+b_w*freq[i];
            }
        }
    }
    else if(fd.name == "wiring_consistency_check_alt"){
        if(addr.size() == 0){
            addr.resize(size/2);
            value.resize(size/2);
            freq.resize(size/2);
        }
        if(addr.size() != size/2){
            addr.resize(size/2,F(0));
            value.resize(size/2);
            freq.resize(size/2);
        }
       
        read_memory_alt(fd,addr,value,freq);
       
        if(fd.stage == 0 && fd.pos != 0){
            for(int i = 0; i < addr.size(); i++){
                v[i] = addr[i]+F(1)+a_w*value[i] + b_w*freq[i];
            }
            int offset = addr.size();
            for(int i = 0; i < addr.size(); i++){
                if(v[i] == F(1)){
                    v[i+offset] = v[i];    
                }else{
                    v[i+offset] = v[i]+b_w;
                }
            }
        }else{
            for(int i = 0; i < addr.size(); i++){
                v[i] = addr[i]+F(1)+a_w*value[i];// + b_w*freq[i];
            }
            int offset = addr.size();
            for(int i = 0; i < addr.size(); i++){
                v[i+offset] = v[i]+b_w*freq[i];
            }
        }
    }
    else{
        for(int i = 0; i < size; i++){
            v[i] = F((i%1024) + 1);
        }
    }
}


void read_stream_PC(stream_descriptor &fd, F *v, int size){
    if(fd.name == "PC_layer"){
        vector<F> buff(size);
        fd.size = fd.size*(1ULL<<fd.layer);
        read_mul_tree_layer(fd,buff,size,fd.layer);
        fd.size = fd.size/(1ULL<<fd.layer);
        for(int i = 0; i < buff.size(); i++){
            v[i] = buff[i];
        }
    }else if(fd.name == "witness"){
        vector<F> buff(size);
        read_stream(fd,buff,size);
        for(int i = 0; i < buff.size(); i++){
            v[i] = buff[i];
        }
    }else if(fd.name == "circuit"){
        if(fd.pos == 0){
            tr_fd.size = circuit_size;
            if(has_lookups){
                tr_fd.size = 2*tr_fd.size;
            }
            mem_fd.size = 4*circuit_size; 
            reset_stream(mem_fd);
            reset_stream(tr_fd);
        }
        if(tr_fd.pos < tr_fd.size/size){
            vector<int> buff_S(size);
            read_circuit_trace(tr_fd,  buff_S);
            if(!has_lookups){
                for(int i = 0; i < size; i++){
                    v[i] = buff_S[i];
                }
            }
            fd.pos++;
        }else if(fd.pos < 9*circuit_size/size){
            vector<F> buff_addr(size/2),buff_f(size/2);
            read_memory_circuit(mem_fd,buff_addr,buff_f);
            for(int i = 0; i < size/2; i++){
                v[2*i] = buff_addr[i];
                v[2*i+1] = buff_f[i];
            }
            fd.pos++;
        }else{
            for(int i = 0; i < size; i++){
                v[i] = F(0);    
            }
        }
        
    }
    else{
        F n = F(322322);
        for(int i = 0; i < size; i++){
            v[i] = n;
            n = n*n+i;
        }
    }
}


void read_mul_tree_layer(stream_descriptor &fd, vector<F> &v, int size, int layer){
    vector<F> temp_v(size);
    for(int i = 0; i < size; i++){
        v[i] = F(1);
    }
    int counter = 0;
    int p = 0;
    if(fd.name == "wiring_consistency_check"){
        while(true){
            read_stream(fd,temp_v,size);
            for(int i = 0; i < size/(1ULL<<layer); i++){
                for(int j = 0; j < 1ULL<<layer; j++){
                    v[counter] *= temp_v[i*(1ULL<<layer) + j];
                }
                counter++;
            }
            if(counter == size){
                break;
            }
        }
    }else{
        temp_v.resize(2*size);
        //printf("%d,%d\n",size,1ULL<<layer);
        while(true){
            read_stream(fd,temp_v,2*size);
            //printf("OK %d,%d,%d\n",v.size(),counter,size);
            for(int i = 0; i < size/(1ULL<<(layer)); i++){
                for(int j = 0; j < 1ULL<<layer; j++){
                    v[counter] *= temp_v[i*(1ULL<<layer) + j];
                }
                for(int j = 0; j < 1ULL<<layer; j++){
                    v[counter+size/2] *= temp_v[i*(1ULL<<layer) + j + size];
                }
                counter++;
            }
            //printf(">OK %d,%d,%d\n",v.size(),counter,size);
            
            if(counter == size/2){
                //printf("~~%d\n",fd.pos);
                break;
            }
        }
    }
    
}

void read_mul_tree_data(stream_descriptor &fd, vector<vector<F>> &v, int size, int layer, int distance){
    int counter = 0;
    int _seg = 1ULL<<(layer);
    vector<F> temp_v(size);
    while(true){
        read_stream(fd,temp_v,size);
        if(fd.name == "wiring_consistency_check"){
            for(int i = 0; i < size/(_seg); i++){
               v[0][counter] = temp_v[i*(_seg)];
                for(int j = 1; j < _seg; j++){
                    v[0][counter] *= temp_v[i*(_seg) + j];
                }
                counter++;
            }
            if(counter == size){
                //printf("OK\n");
                break;
            }
    
        }else{
            for(int i = 0; i < size/(2*_seg); i++){
                v[0][counter] = temp_v[i*(_seg)];
                for(int j = 1; j < _seg; j++){
                    v[0][counter] *= temp_v[i*(_seg) + j];
                }
                v[0][counter+size/2] = temp_v[i*(_seg) + size/2];
                for(int j = 1; j < _seg; j++){
                    v[0][counter+size/2] *= temp_v[i*(_seg) + j+ size/2];
                }
                counter++;
            }
            if(counter == size/2){
                //printf("OK\n");
                break;
            }
        }
        
    }
    //printf("%d\n",distance);
    int offset = 1<<distance;
    
    //printf("%d,%d,%d\n",offset,v[0].size(),offset*v[1].size());
    for(int i = 1; i < v.size(); i++){
        for(int j = 0; j < v[i].size(); j++){
            v[i][j] = F(1);
            for(int k = 0; k < offset; k++){
                v[i][j] *= v[i-1][offset*j + k];
            }
        } 
    }
}