#include<iostream>
#include<pin.H>
#include<stdio.h>
#include<fstream>
#include<string>
#include<utility>
#include<cstring>
#include<map>
using namespace std;

map<pair<ADDRINT, ADDRINT>, UINT64> loop_cnt;
map<ADDRINT, string> if_cnt;

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "key.txt", "Specify output filename: ");
ofstream outfile;

UINT64 key_val = 0;

VOID decode(ADDRINT ip, ADDRINT target, BOOL istaken){
    if((target < ip) && istaken){
        auto val = make_pair(target, ip);
        loop_cnt[val]++;
    }
    else if(target > ip){
        if(!istaken){
            if_cnt[ip] += "1";
        }
        else{
            if_cnt[ip] += "0";
        }
    }
}


VOID Instruction(INS ins, VOID* v){
    if(INS_IsBranch(ins) && INS_HasFallThrough(ins)){
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)decode, IARG_INST_PTR, IARG_BRANCH_TARGET_ADDR, IARG_BRANCH_TAKEN, IARG_END);
    }
}

VOID Fini(INT32 code, VOID* v){
    for(auto u : if_cnt){
        ADDRINT pc = u.first;
        for(auto v : loop_cnt){
            if((v.second==(UINT64)63) && (v.first.first <= pc) && (v.first.second > pc)){
                for (char c : u.second) key_val = (key_val << 1) | (c == '1' ? 1ULL : 0ULL);
                outfile << key_val << endl;
                outfile.close();
                return;
            }
        }
    }
    outfile << key_val << endl;
    outfile.close();
}


INT32 Usage(){
    cerr << "This Pintool tries to find the RSA key from the 64-bit executable of binary exponentiation algorithm" << endl;
    cerr << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}


int main(int argc, char*argv[]){
    if(PIN_Init(argc, argv)) return Usage();
    outfile.open(KnobOutputFile.Value().c_str());
    
    INS_AddInstrumentFunction(Instruction, 0);

    PIN_AddFiniFunction(Fini, 0);

    PIN_StartProgram();
    return 0;
}
