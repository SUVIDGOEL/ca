#include<iostream>
#include<stdio.h>
#include<pin.H>
#include<fstream>
#include<string.h>
#include<cstring>
#include<string>
using namespace std;

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "results.out", "specify output filename:");
ofstream outfile;

string sarr[] = {"LOADS: ", "STORES: ", "NOPS: ", "DIRECT_CALL: ", "INDIRECT_CALL: ", "RETURN: ", "UNCONDITIONAL_BRANCH: ", "CONDITIONAL_BRANCH: ", "LOGICAL: ", "ROTATE_AND_SHIFT: ", "FLAG_OP: ", "VECTOR: "                 , "CONDITIONAL_MOVE: ", "MMX_SSE: ", "SYSCALL: ", "FLOATING_POINT: ",  "OTHERS: "}               
}

typedef struct instruction_counts{
   UINT64 _load;
   UINT64 _store;
   UINT64 _nop;
   UINT64 _dir_call;
   UINT64 _indir_call;
   UINT64 _ret;
   UINT64 _uncond_br;
   UINT64 _cond_br;
   UINT64 _logic_op;
   UINT64 _rot_sht;
   UINT64 _flag_op;
   UINT64 _vect_ins;
   UINT64 _cond_mov;
   UINT64 _mmx_sse;
   UINT64 _syscalls;
   UINT64 _fp_ins;
   UINT64 _others;
}inst_cnt;

typedef struct temporary_counts{
   UINT64 _load;
   UINT64 _store;
   UINT64 _nop;
   UINT64 _dir_call;
   UINT64 _indir_call;
   UINT64 _ret;
   UINT64 _uncond_br;
   UINT64 _cond_br;
   UINT64 _logic_op;
   UINT64 _rot_sht;
   UINT64 _flag_op;
   UINT64 _vect_ins;
   UINT64 _cond_mov;
   UINT64 _mmx_sse;
   UINT64 _syscalls;
   UINT64 _fp_ins;
   UINT64 _others;
}temp_cnt;

inst_cnt* ic = NULL;

VOID do_cnt(UINT64* c){
    (*c)++;
}

VOID mem_access(UINT64 cnt, UINT64* c){
    (*c)+=cnt;
}

VOID Instruction(INS ins, VOID* v){
    temp_cnt* tc = new temp_cnt;
    memset(tc, 0x00, sizeof(temp_cnt));

    for(BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)){
        
    }

    UINT32 memOperands = INS_MemoryOperandCount(ins);
    if(memOperands){
        for(UINT32 memOp=0; memOp < memOperands; memOp++){
            
            UINT64 size = INS_MemoryOperandSize(ins, memOp);
            UINT64 rem = size%((UINT64)0x20);
            UINT64 rounds = size/(UINT64)0x20;
            UINT64 cnt = (rem>0) ? rounds+1 : rounds;

            if(INS_MemoryOperandIsRead(ins, memOp)){
                INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT64, cnt, IARG_PTR, &(ic->_load), IARG_END);
            }
            else if(INS_MemoryOperandIsWritten(ins, memOp)){
                INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT64, cnt, IARG_PTR, &(ic->_store), IARG_END);
            }
        }
    }
    if(INS_Category(ins) == XED_CATEGORY_NOP){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_nop), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_CALL){
        if(INS_IsDirectCall(ins)) INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_dir_call), IARG_END);
        else if(INS_IsIndirectCall(ins)) INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_indir_call), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_RET){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_ret), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_UNCOND_BR){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_uncond_br), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_COND_BR){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_br), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_LOGICAL){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_logic_op), IARG_END);
    }
    else if((INS_Category(ins) == XED_CATEGORY_ROTATE) || (INS_Category(ins) == XED_CATEGORY_SHIFT)){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_rot_sht), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_FLAGOP){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_flag_op), IARG_END);
    }
    else if((INS_Category(ins) == XED_CATEGORY_AVX) || (INS_Category(ins) == XED_CATEGORY_AVX2) || (INS_Category(ins) == XED_CATEGORY_AVX2GATHER) || (INS_Category(ins) == XED_CATEGORY_AVX512)){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_vect_ins), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_CMOV){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_mov), IARG_END);
    } 
    else if((INS_Category(ins) == XED_CATEGORY_MMX) || (INS_Category(ins) == XED_CATEGORY_SSE)){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_mmx_sse), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_SYSCALL){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_syscalls), IARG_END);
    }
    else if(INS_Category(ins) == XED_CATEGORY_X87_ALU){
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_fp_ins), IARG_END);
    }
    else {
        INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_others), IARG_END);
    }

}

VOID Fini(INT32 code, VOID* v){
    unsigned char* ptr = ic;
    int i = 0;
    while(i<17){
        outfile << sarr[i] << *ptr << '\n';
        i++;
        ptr += 8;
    }
     
    outfile.close();
}

int main(int argc, char* argv[]){
	if(PIN_Init(argc, argv)) return 1;
	PIN_InitSymbols();
    outfile.open(KnobOutputFile.Value().c_str());
    
    ic = new inst_cnt;
    memset(ic, 0x00, sizeof(inst_cnt));

    INS_AddInstrumentFunction(Instruction, 0);

	PIN_AddFiniFunction(Fini, 0);
	PIN_StartProgram();
	return 0;
}
