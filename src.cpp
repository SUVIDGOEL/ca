#include<iostream>
#include<stdio.h>
#include<pin.H>
#include<fstream>
#include<string.h>
#include<cstring>
#include<string>
#include<set>
using namespace std;

set<ADDRINT> instr_mem;
set<ADDRINT> data_mem;
vector<ADDRINT> inst_size(16, 0);
vector<ADDRINT> inst_operands(16, 0);
vector<ADDRINT> inst_read_oper(16, 0);
vector<ADDRINT> inst_write_oper(16, 0);
vector<ADDRINT> inst_memop(16, 0);
vector<ADDRINT> inst_read_cnt(16, 0);
vector<ADDRINT> inst_write_cnt(16, 0);
ADDRINT total_data_mem=0;
ADDRINT max_data_mem=0;
ADDRINT mem_instr_cnt = 0;
INT32 max_imm = 0;
INT32 min_imm = 1e9;
ADDRDELTA max_disp = 0;
ADDRDELTA min_disp = 1e9;

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "results.out", "specify output filename:");
KNOB<UINT64> KnobFastForwardCount(KNOB_MODE_WRITEONCE, "pintool", "f", "", "specify the fast forward amount:");

ofstream outfile;

UINT64 fast_forward_count;
UINT64 icnt = 0;

string sarr[] = {"LOADS: ", "STORES: ", "NOPS: ", "DIRECT_CALL: ", "INDIRECT_CALL: ", "RETURN: ", "UNCONDITIONAL_BRANCH: ", "CONDITIONAL_BRANCH: ", "LOGICAL: ", "ROTATE_AND_SHIFT: ", "FLAG_OP: ", "VECTOR: "                 , "CONDITIONAL_MOVE: ", "MMX_SSE: ", "SYSCALL: ", "FLOATING_POINT: ",  "OTHERS: ", "INST_FOOTPRINT: ", "DATA_FOOTPRINT: ", "SINGLE_CHUNK_INSTRUCTIONS: ", "MULTIPLE_CHUNK_INSTRUCTIONS",
                   "SINGLE_DATA_CHUNK: ", "MULTIPLE_DATA_CHUNK: "};

//Struct for stroring varioius types of counts
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
   UINT64 _inst_foot;
   UINT64 _data_foot;
   UINT64 _single_inst_chunk;
   UINT64 _mult_inst_chunk;
   UINT64 _single_data_chunk;
   UINT64 _mult_data_chunk;
}inst_cnt;

inst_cnt* ic = NULL;

//ANALYSIS CALLS--------------------------------------------

//Analysis Call for incrementing number of instructions executed
VOID ins_cnt(){
    icnt++;
}

//Analysis Call for checking fast forwarding Condition
ADDRINT fast_forward(){
    return (icnt >= fast_forward_count) && (icnt < fast_forward_count + 1000000000);
}

//Analysis Call for checking termination condition
ADDRINT terminate(){
    return (icnt >= fast_forward_count + 1000000000);
}

//Analysis Call for incrementing count values
VOID do_cnt(UINT64* c){
    (*c)++;
}

//Analysis Call for counting number of 4 byte data memory read or writes
VOID mem_access(UINT64 cnt, UINT64* c){
    (*c)+=cnt;
}

//Analysis Calls for counting unique instruction memory chunks at 32 byte granularity
VOID instruction_analysis(ADDRINT ip1, ADDRINT ip, ADDRINT sz, ADDRINT oper, ADDRINT r, ADDRINT wr, INT32 max_imm_val, INT32 min_imm_val){
    UINT64 cnt = 0;
    inst_size[sz]++;
    inst_operands[oper]++;
    inst_read_oper[r]++;
    inst_write_oper[wr]++;
    if(max_imm < max_imm_val) max_imm = max_imm_val;
    if(min_imm > min_imm_val) min_imm = min_imm_val;
    for(; ip1 < ip + sz; ip1 += (ADDRINT)32){
        if(instr_mem.find(ip1)==instr_mem.end()){
            instr_mem.insert(ip1);
            cnt++;
        }
    }
    if(cnt>1)ic->_mult_inst_chunk += 1;
    else if(cnt==1)ic->_single_inst_chunk += 1;
}

//
VOID instr_analysis_predicated(UINT32 memop, UINT32 read_cnt, UINT32 write_cnt, ADDRINT mem_size_sum, ADDRDELTA max_mem_disp, ADDRDELTA min_mem_disp){
    inst_memop[memop]++;
    inst_read_cnt[read_cnt]++;
    inst_write_cnt[write_cnt]++;
    
    total_data_mem += mem_size_sum;
    if(mem_size_sum > max_data_mem)max_data_mem = mem_size_sum;
    mem_instr_cnt++;

    if(max_mem_disp > max_disp)max_disp = max_mem_disp;
    if(min_mem_disp < min_disp)min_disp = min_mem_disp;
}

//Analysis call for counting unique data memory chunks at 32 byte granularity
VOID data_mem_count(UINT64* ptr1, UINT64*ptr2, ADDRINT addr, UINT64 sz){ //CORRECT THIS CODE--------------------------------------------------------------------------------------------
    ADDRINT add = (addr>>5)<<5;
    UINT64 cnt = 0;
    for(; add < addr + sz; add += (ADDRINT)32){
        if(data_mem.find(add)==data_mem.end()){
            data_mem.insert(add);
            cnt++;
        }
    }
    if(cnt > 1) (*ptr2)++;
    else if(cnt==1) (*ptr1)++;
}


//Analysis Call for terminating the pintool after 1000,000,000 have been instrumented or benchmark application finishes
VOID exit_routine(){
    unsigned char* ptr = (unsigned char*)ic;
    int i = 0;
    while(i<21){
        outfile << sarr[i] << *ptr << '\n';
        i++;
        ptr += 8;
    }
     
    outfile.close();
    exit(0);
}


//Instrumentation Callback-----------------------------------

inline void Instruction_Count(INS ins){
     
    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
    //INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR));
    
    ADDRINT sz = INS_Size(ins);
    ADDRINT ip = INS_Address(ins);
    ADDRINT ip1 = (ip>>5)<<5;
    ADDRINT oper = INS_OperandCount(ins);
    INT32 max_imm_val = 0;
    INT32 min_imm_val = 1e9;
    if(oper){
        for(ADDRINT op = 0; op < oper; op++){
            if(INS_OperandIsImmediate(ins, op)){
                INT32 imm_val = INS_OperandImmediate(ins, op);
                if(imm_val > max_imm_val)max_imm_val = imm_val;
                if(imm_val < min_imm_val)min_imm_val = imm_val;
            }
        }
    }
    ADDRINT r = INS_MaxNumRRegs(ins);
    ADDRINT wr = INS_MaxNumWRegs(ins);
   
    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
    INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)instruction_analysis, IARG_ADDRINT, ip1, 
                       IARG_ADDRINT, ip, IARG_ADDRINT, sz, IARG_ADDRINT, oper, 
                       IARG_ADDRINT, r, IARG_ADDRINT, wr, IARG_ADDRINT, max_imm_val, IARG_ADDRINT, min_imm_val, IARG_END);
    

    UINT32 memOperands = INS_MemoryOperandCount(ins);
    UINT32 read_count = 0;
    UINT32 write_count = 0;
    ADDRINT mem_size_sum = 0;
    ADDRDELTA min_mem_disp = 1e9;
    ADDRDELTA max_mem_disp = 0;
    if(memOperands){
        for(UINT32 memOp=0; memOp < memOperands; memOp++){
            
            ADDRDELTA mem_disp = INS_OperandMemoryDisplacement(ins, memOp);
            if(mem_disp > max_mem_disp)max_mem_disp = mem_disp;
            if(mem_disp < min_mem_disp)min_mem_disp = mem_disp;
            UINT64 size = INS_MemoryOperandSize(ins, memOp);
            mem_size_sum += size;
            UINT64 rem = size%((UINT64)0x20);
            UINT64 rounds = size>>5;
            UINT64 cnt = (rem>0) ? rounds+1 : rounds;

            if(INS_MemoryOperandIsRead(ins, memOp)){
                read_count++;
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)data_mem_count, 
                                         IARG_PTR, &(ic->_single_data_chunk), 
                                         IARG_PTR, &(ic->_mult_data_chunk), IARG_MEMORYOP_EA, memOp, 
                                         IARG_UINT64, size, IARG_END);

                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
                INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT64, cnt, IARG_PTR, &(ic->_load), IARG_END);
            }
            else if(INS_MemoryOperandIsWritten(ins, memOp)){
                write_count++;
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
                INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)data_mem_count, 
                                         IARG_PTR, &(ic->_single_data_chunk), 
                                         IARG_PTR, &(ic->_mult_data_chunk), IARG_MEMORYOP_EA, memOp, 
                                         IARG_UINT64, size, IARG_END);

                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
                INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT64, cnt, IARG_PTR, &(ic->_store), IARG_END);
            }
        }
        
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
        INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)instr_analysis_predicated, IARG_UINT32, memOperands, 
                                     IARG_UINT32, read_count, IARG_UINT32, write_count, IARG_ADDRINT, mem_size_sum, 
                                     IARG_ADDRINT, max_mem_disp, IARG_ADDRINT, min_mem_disp, IARG_END);
        
    }

    UINT64* ptr = NULL;
    
    if(INS_Category(ins) == XED_CATEGORY_NOP){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_nop), IARG_END);
        ptr = &(ic->_nop);
    }
    else if(INS_Category(ins) == XED_CATEGORY_CALL){
        if(INS_IsDirectCall(ins)) {
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_dir_call), IARG_END);
            ptr = &(ic->_dir_call);
        }
        else {
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_indir_call), IARG_END);
            ptr = &(ic->_indir_call);
        }
    }
    else if(INS_Category(ins) == XED_CATEGORY_RET){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_ret), IARG_END);
        ptr = &(ic->_ret);
    }
    else if(INS_Category(ins) == XED_CATEGORY_UNCOND_BR){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_uncond_br), IARG_END);
        ptr = &(ic->_uncond_br);
    }   
    else if(INS_Category(ins) == XED_CATEGORY_COND_BR){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_br), IARG_END);
        ptr = &(ic->_cond_br);
    }
    else if(INS_Category(ins) == XED_CATEGORY_LOGICAL){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_logic_op), IARG_END);
        ptr = &(ic->_logic_op);
    }
    else if((INS_Category(ins) == XED_CATEGORY_ROTATE) || (INS_Category(ins) == XED_CATEGORY_SHIFT)){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_rot_sht), IARG_END);
        ptr = &(ic->_rot_sht);
    }
    else if(INS_Category(ins) == XED_CATEGORY_FLAGOP){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_flag_op), IARG_END);
        ptr = &(ic->_flag_op);
    }
    else if((INS_Category(ins) == XED_CATEGORY_AVX) || (INS_Category(ins) == XED_CATEGORY_AVX2) || (INS_Category(ins) == XED_CATEGORY_AVX2GATHER) || (INS_Category(ins) == XED_CATEGORY_AVX512)){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_vect_ins), IARG_END);
        ptr = &(ic->_vect_ins);
    }
    else if(INS_Category(ins) == XED_CATEGORY_CMOV){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_mov), IARG_END);
        ptr = &(ic->_cond_mov);
    } 
    else if((INS_Category(ins) == XED_CATEGORY_MMX) || (INS_Category(ins) == XED_CATEGORY_SSE)){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_mmx_sse), IARG_END);
        ptr = &(ic->_mmx_sse);
    }
    else if(INS_Category(ins) == XED_CATEGORY_SYSCALL){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_syscalls), IARG_END);
        ptr = &(ic->_syscalls);    
    }
    else if(INS_Category(ins) == XED_CATEGORY_X87_ALU){
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_fp_ins), IARG_END);
        ptr = &(ic->_fp_ins);
    }
    else {
        //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_others), IARG_END);
        ptr = &(ic->_others);
    }

    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, ptr, IARG_END);

    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_cnt, IARG_END);
}


//Instrumentation Function
VOID Instruction(INS ins, VOID* v){
    
    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)terminate, IARG_END);
    INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)exit_routine, IARG_END);

    Instruction_Count(ins);   
}

//Fini Function, Although it will not be used since we will terminate using exit_routine.
VOID Fini(INT32 code, VOID* v){
    
    exit_routine();
}

//Usage Function
INT32 Usage(){
    cerr << "This Tool Performs Instruction level Instrumentation on benchmark programs\n";
    cerr << KNOB_BASE::StringKnobSummary() << '\n';
    return 1;
}

int main(int argc, char* argv[]){
	if(PIN_Init(argc, argv)) return Usage();

	PIN_InitSymbols();
    outfile.open(KnobOutputFile.Value().c_str());

    fast_forward_count = KnobFastForwardCount.Value();
    cout << "Fast Forward Count: " << fast_forward_count << '\n';
    
    ic = new inst_cnt;
    memset(ic, 0x00, sizeof(inst_cnt));

    INS_AddInstrumentFunction(Instruction, 0);

	PIN_AddFiniFunction(Fini, 0);
	PIN_StartProgram();
	
    return 0;
}
