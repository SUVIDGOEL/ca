#include<iostream>
#include<pin.H>
#include<fstream>
#include<cstring>
#include<string>
#include<unordered_set>
#include<vector>
using namespace std;

unordered_set<UINT32> instr_mem;
unordered_set<UINT32> data_mem;
vector<UINT32> inst_size(16, 0);
vector<UINT32> inst_operands(8, 0);
vector<UINT32> inst_read_oper(8, 0);
vector<UINT32> inst_write_oper(8, 0);
vector<ADDRINT> inst_memop(8, 0);
vector<ADDRINT> inst_read_cnt(8, 0);
vector<ADDRINT> inst_write_cnt(8, 0);
ADDRINT total_data_mem=0;
ADDRINT max_data_mem=0;
ADDRINT mem_instr_cnt = 0;
INT32 max_imm = INT_MIN;
INT32 min_imm = INT_MAX;
ADDRDELTA max_disp = INT_MIN;
ADDRDELTA min_disp = INT_MAX;

KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "results.out", "specify output filename:");
KNOB<UINT64> KnobFastForwardCount(KNOB_MODE_WRITEONCE, "pintool", "f", "0", "specify the fast forward amount:");

ofstream* outfile;

UINT64 fast_forward_count;
static UINT64 icnt = 0;

const char* sarr[] = {"LOADS: ", "STORES: ", "NOPS: ", "DIRECT_CALL: ", "INDIRECT_CALL: ", "RETURN: ", "UNCONDITIONAL_BRANCH: ", "CONDITIONAL_BRANCH: ", "LOGICAL: ", "ROTATE_AND_SHIFT: ", "FLAG_OP: ", 
                      "VECTOR: ", "CONDITIONAL_MOVE: ", "MMX_SSE: ", "SYSCALL: ", "FLOATING_POINT: ",  "OTHERS: ", "INST_FOOTPRINT: ", "DATA_FOOTPRINT: ", "SINGLE_CHUNK_INSTRUCTIONS: ", 
                      "MULTIPLE_CHUNK_INSTRUCTIONS", "SINGLE_DATA_CHUNK: ", "MULTIPLE_DATA_CHUNK: "};

//Struct for stroring varioius types of counts
typedef struct instruction_counts{
   UINT32 _load;
   UINT32 _store;
   UINT32 _nop;
   UINT32 _dir_call;
   UINT32 _indir_call;
   UINT32 _ret;
   UINT32 _uncond_br;
   UINT32 _cond_br;
   UINT32 _logic_op;
   UINT32 _rot_sht;
   UINT32 _flag_op;
   UINT32 _vect_ins;
   UINT32 _cond_mov;
   UINT32 _mmx_sse;
   UINT32 _syscalls;
   UINT32 _fp_ins;
   UINT32 _others;
   UINT32 _inst_foot;
   UINT32 _data_foot;
   UINT32 _single_inst_chunk;
   UINT32 _mult_inst_chunk;
   UINT32 _single_data_chunk;
   UINT32 _mult_data_chunk;
}inst_cnt;

inst_cnt ic = {0};

//static bool first = true;

//ANALYSIS CALLS--------------------------------------------

//Analysis Call for incrementing number of instructions executed
VOID PIN_FAST_ANALYSIS_CALL ins_cnt(){
   
    icnt++;
}

//Analysis Call for checking fast forwarding Condition
ADDRINT PIN_FAST_ANALYSIS_CALL fast_forward_check(){
    return (icnt >= fast_forward_count) && (icnt < fast_forward_count + (UINT64)1000000000);
}

ADDRINT fast_forward_fail(){
    return (icnt < fast_forward_count);
}

//Analysis Call for checking termination condition
ADDRINT PIN_FAST_ANALYSIS_CALL terminate_check(){
    return (icnt >= fast_forward_count + (UINT64)1000000000);
}

//Analysis Call for incrementing count values
VOID PIN_FAST_ANALYSIS_CALL do_cnt(UINT32* c){
    //cout << "Inside do_cnt function" << '\n';
    (*c)++;
}

//Analysis Call for counting number of 4 byte data memory read or writes
VOID PIN_FAST_ANALYSIS_CALL mem_access(UINT32 cnt, UINT32* c){
    (*c)+=cnt;
}

//Analysis Calls for counting unique instruction memory chunks at 32 byte granularity
VOID instruction_analysis(ADDRINT ip1, ADDRINT ip, ADDRINT sz, UINT32 oper, UINT32 r, UINT32 wr, INT32 max_imm_val, INT32 min_imm_val){
    //inst_size[sz]++;
    //inst_operands[oper]++;
    //inst_read_oper[r]++;
    //inst_write_oper[wr]++;
    
    //cerr << "Inside instruction analysis" << endl;

    if (sz < inst_size.size()) inst_size[sz]++;
    if (oper < inst_operands.size()) inst_operands[oper]++;
    if (r < inst_read_oper.size()) inst_read_oper[r]++;
    if (wr < inst_write_oper.size()) inst_write_oper[wr]++;

    ADDRINT start = ip1 >> 5;
    ADDRINT end = (ip+sz)>>5;
    ADDRINT cnt = 0;

    if(max_imm < max_imm_val) max_imm = max_imm_val;
    if(min_imm > min_imm_val) min_imm = min_imm_val;
    for(ADDRINT i = start; i <= end; i++){
        if(instr_mem.find(i)==instr_mem.end()){
            instr_mem.insert(i);
            cnt++;
        }
    }
    if(cnt>1)ic._mult_inst_chunk += 1;
    else if(cnt==1)ic._single_inst_chunk += 1;
}


VOID instr_analysis_predicated(UINT32 memop, UINT32 read_cnt, UINT32 write_cnt, ADDRINT mem_size_sum, ADDRDELTA max_mem_disp, ADDRDELTA min_mem_disp){
    //inst_memop[memop]++;
    //inst_read_cnt[read_cnt]++;
    //inst_write_cnt[write_cnt]++;
    
    if(memop < inst_memop.size())   inst_memop[memop]++;
    if(read_cnt < inst_read_cnt.size())  inst_read_cnt[read_cnt]++;
    if(write_cnt < inst_write_cnt.size()) inst_write_cnt[write_cnt]++;

    total_data_mem += mem_size_sum;
    if(mem_size_sum > max_data_mem)max_data_mem = mem_size_sum;
    mem_instr_cnt++;

    if(max_mem_disp > max_disp)max_disp = max_mem_disp;
    if(min_mem_disp < min_disp)min_disp = min_mem_disp;
}

//Analysis call for counting unique data memory chunks at 32 byte granularity
VOID data_mem_count(UINT32* ptr1, UINT32* ptr2, ADDRINT addr, ADDRINT sz){ //CORRECTED THIS CODE--------------------------------------------------------------------------------------------
    
    ADDRINT start = addr >> 5;
    ADDRINT end = (addr + sz) >> 5;
    ADDRINT cnt = 0;
    for(ADDRINT i=start; i <= end; i++){
        if(data_mem.find(i)==data_mem.end()){
            data_mem.insert(i);
            cnt++;
        }
    }
    if(cnt > 1) (*ptr2)++;
    else if(cnt==1) (*ptr1)++;
}


//Analysis Call for terminating the pintool after 1000,000,000 have been instrumented or benchmark application finishes
VOID exit_routine(){
    ic._inst_foot = (UINT32)instr_mem.size();
    ic._data_foot = (UINT32)data_mem.size();

    // ── PART A: Instruction counts and percentages ──────────────────────────
    UINT64 total = (UINT64)ic._load + ic._store + ic._nop + ic._dir_call +
                   ic._indir_call + ic._ret + ic._uncond_br + ic._cond_br +
                   ic._logic_op + ic._rot_sht + ic._flag_op + ic._vect_ins +
                   ic._cond_mov + ic._mmx_sse + ic._syscalls + ic._fp_ins + ic._others;

    *outfile << "===== PART A: Instruction Mix =====" << endl;
    *outfile << "LOADS: "               << ic._load       << " (" << 100.0*ic._load/total       << "%)" << endl;
    *outfile << "STORES: "              << ic._store      << " (" << 100.0*ic._store/total      << "%)" << endl;
    *outfile << "NOPS: "                << ic._nop        << " (" << 100.0*ic._nop/total        << "%)" << endl;
    *outfile << "DIRECT_CALLS: "        << ic._dir_call   << " (" << 100.0*ic._dir_call/total   << "%)" << endl;
    *outfile << "INDIRECT_CALLS: "      << ic._indir_call << " (" << 100.0*ic._indir_call/total << "%)" << endl;
    *outfile << "RETURNS: "             << ic._ret        << " (" << 100.0*ic._ret/total        << "%)" << endl;
    *outfile << "UNCONDITIONAL_BR: "    << ic._uncond_br  << " (" << 100.0*ic._uncond_br/total  << "%)" << endl;
    *outfile << "CONDITIONAL_BR: "      << ic._cond_br    << " (" << 100.0*ic._cond_br/total    << "%)" << endl;
    *outfile << "LOGICAL: "             << ic._logic_op   << " (" << 100.0*ic._logic_op/total   << "%)" << endl;
    *outfile << "ROTATE_AND_SHIFT: "    << ic._rot_sht    << " (" << 100.0*ic._rot_sht/total    << "%)" << endl;
    *outfile << "FLAG_OP: "             << ic._flag_op    << " (" << 100.0*ic._flag_op/total    << "%)" << endl;
    *outfile << "VECTOR: "              << ic._vect_ins   << " (" << 100.0*ic._vect_ins/total   << "%)" << endl;
    *outfile << "CONDITIONAL_MOVE: "    << ic._cond_mov   << " (" << 100.0*ic._cond_mov/total   << "%)" << endl;
    *outfile << "MMX_SSE: "             << ic._mmx_sse    << " (" << 100.0*ic._mmx_sse/total    << "%)" << endl;
    *outfile << "SYSCALL: "             << ic._syscalls   << " (" << 100.0*ic._syscalls/total   << "%)" << endl;
    *outfile << "FLOATING_POINT: "      << ic._fp_ins     << " (" << 100.0*ic._fp_ins/total     << "%)" << endl;
    *outfile << "OTHERS: "              << ic._others     << " (" << 100.0*ic._others/total     << "%)" << endl;
    *outfile << "TOTAL: "               << total << endl;

    // ── PART B: CPI ─────────────────────────────────────────────────────────
    // loads and stores cost 70 cycles, everything else costs 1 cycle
    UINT64 total_cycles = ((UINT64)ic._load + ic._store) * 70 +
                          ((UINT64)ic._nop + ic._dir_call + ic._indir_call + ic._ret +
                           ic._uncond_br + ic._cond_br + ic._logic_op + ic._rot_sht +
                           ic._flag_op + ic._vect_ins + ic._cond_mov + ic._mmx_sse +
                           ic._syscalls + ic._fp_ins + ic._others) * 1;

    double cpi = (total > 0) ? (double)total_cycles / (double)total : 0.0;
    *outfile << endl << "===== PART B: CPI =====" << endl;
    *outfile << "TOTAL_CYCLES: " << total_cycles << endl;
    *outfile << "TOTAL_INSTRUCTIONS: " << total << endl;
    *outfile << "CPI: " << cpi << endl;

    // ── PART C: Memory Footprints ────────────────────────────────────────────
    *outfile << endl << "===== PART C: Memory Footprint =====" << endl;
    *outfile << "INSTRUCTION_CHUNKS (32B): " << ic._inst_foot << endl;
    *outfile << "INSTRUCTION_FOOTPRINT (bytes): " << (UINT64)ic._inst_foot * 32 << endl;
    *outfile << "DATA_CHUNKS (32B): " << ic._data_foot << endl;
    *outfile << "DATA_FOOTPRINT (bytes): " << (UINT64)ic._data_foot * 32 << endl;
    *outfile << "SINGLE_CHUNK_INSTRUCTIONS: " << ic._single_inst_chunk << endl;
    *outfile << "MULTIPLE_CHUNK_INSTRUCTIONS: " << ic._mult_inst_chunk << endl;
    *outfile << "SINGLE_DATA_CHUNK_ACCESSES: " << ic._single_data_chunk << endl;
    *outfile << "MULTIPLE_DATA_CHUNK_ACCESSES: " << ic._mult_data_chunk << endl;

    // ── PART D: ISA Properties ───────────────────────────────────────────────
    *outfile << endl << "===== PART D: ISA Properties =====" << endl;

    // D1: Instruction length distribution
    *outfile << endl << "-- D1: Instruction Length Distribution --" << endl;
    for(int i = 1; i < (int)inst_size.size(); i++){
        *outfile << "LENGTH_" << i << "_BYTES: " << inst_size[i] << endl;
    }

    // D2: Operand count distribution
    *outfile << endl << "-- D2: Operand Count Distribution --" << endl;
    for(int i = 0; i < (int)inst_operands.size(); i++){
        *outfile << "OPERANDS_" << i << ": " << inst_operands[i] << endl;
    }

    // D3: Register read operand distribution
    *outfile << endl << "-- D3: Register Read Operand Distribution --" << endl;
    for(int i = 0; i < (int)inst_read_oper.size(); i++){
        *outfile << "REG_READ_" << i << ": " << inst_read_oper[i] << endl;
    }

    // D4: Register write operand distribution
    *outfile << endl << "-- D4: Register Write Operand Distribution --" << endl;
    for(int i = 0; i < (int)inst_write_oper.size(); i++){
        *outfile << "REG_WRITE_" << i << ": " << inst_write_oper[i] << endl;
    }

    // D5: Memory operand distribution
    *outfile << endl << "-- D5: Memory Operand Distribution --" << endl;
    for(int i = 0; i < (int)inst_memop.size(); i++){
        *outfile << "MEM_OPERANDS_" << i << ": " << inst_memop[i] << endl;
    }

    // D6: Memory read operand distribution
    *outfile << endl << "-- D6: Memory Read Operand Distribution --" << endl;
    for(int i = 0; i < (int)inst_read_cnt.size(); i++){
        *outfile << "MEM_READ_" << i << ": " << inst_read_cnt[i] << endl;
    }

    // D7: Memory write operand distribution
    *outfile << endl << "-- D7: Memory Write Operand Distribution --" << endl;
    for(int i = 0; i < (int)inst_write_cnt.size(); i++){
        *outfile << "MEM_WRITE_" << i << ": " << inst_write_cnt[i] << endl;
    }

    // D8: Max and average memory bytes touched per memory instruction
    double avg_mem = (mem_instr_cnt > 0) ? (double)total_data_mem / (double)mem_instr_cnt : 0.0;
    *outfile << endl << "-- D8: Memory Bytes per Memory Instruction --" << endl;
    *outfile << "MAX_MEM_BYTES: " << max_data_mem << endl;
    *outfile << "AVG_MEM_BYTES: " << avg_mem << endl;

    // D9: Max and min immediate values
    *outfile << endl << "-- D9: Immediate Field Values --" << endl;
    *outfile << "MAX_IMMEDIATE: " << max_imm << endl;
    *outfile << "MIN_IMMEDIATE: " << min_imm << endl;

    // D10: Max and min displacement values
    *outfile << endl << "-- D10: Displacement Field Values --" << endl;
    *outfile << "MAX_DISPLACEMENT: " << max_disp << endl;
    *outfile << "MIN_DISPLACEMENT: " << min_disp << endl;

    outfile->close();
    exit(0);
    //PIN_ExitApplication(0);
}

VOID early_exit(){
    exit_routine();
    PIN_ExitApplication(0);
}


//Instrumentation Callback-----------------------------------

inline void Instruction_Count(BBL bbl){
     
    //cerr << "Inside inline Instruction Count function" << endl;
    //INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward, IARG_END);
    //INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR));
    for(INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)){

        ADDRINT sz = INS_Size(ins);
        ADDRINT ip = INS_Address(ins);
        //cerr << "IP: " << (UINT32)ip << endl; 
        ADDRINT ip1 = (ip>>5)<<5;
        UINT32 oper = INS_OperandCount(ins);
        INT32 max_imm_val = 0;
        INT32 min_imm_val = INT32_MAX;
        if(oper){
            for(UINT32 op = 0; op < oper; op++){
                if(INS_OperandIsImmediate(ins, op)){
                    INT32 imm_val = INS_OperandImmediate(ins, op);
                    if(imm_val > max_imm_val)max_imm_val = imm_val;
                    if(imm_val < min_imm_val)min_imm_val = imm_val;
                }
            }
        }
        UINT32 r = INS_MaxNumRRegs(ins);
        UINT32 wr = INS_MaxNumWRegs(ins);
       
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
        INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)instruction_analysis, IARG_ADDRINT, ip1, 
                           IARG_ADDRINT, ip, IARG_ADDRINT, sz, IARG_UINT32, oper, 
                           IARG_UINT32, r, IARG_UINT32, wr, IARG_ADDRINT, max_imm_val, IARG_ADDRINT, min_imm_val, IARG_END);
        

        UINT32 memOperands = INS_MemoryOperandCount(ins);
        UINT32 read_count = 0;
        UINT32 write_count = 0;
        //cerr << "memop: " << memOperands << " read cnt: " << read_count << " write_count: " << write_count << endl;
        ADDRINT mem_size_sum = 0;
        ADDRDELTA min_mem_disp = 1e9;
        ADDRDELTA max_mem_disp = 0;
        if(memOperands >= 0){
            for(UINT32 memOp=0; memOp < memOperands; memOp++){
                
                UINT32 op_id = INS_MemoryOperandIndexToOperandIndex(ins, memOp);
                ADDRDELTA mem_disp = INS_OperandMemoryDisplacement(ins, op_id);
                if(mem_disp > max_mem_disp)max_mem_disp = mem_disp;
                if(mem_disp < min_mem_disp)min_mem_disp = mem_disp;
                ADDRINT size = INS_MemoryOperandSize(ins, memOp);
                mem_size_sum += size;
                ADDRINT rem = size%((ADDRINT)4);
                ADDRINT rounds = size>>2;
                UINT32 cnt = (rem>0) ? rounds+1 : rounds;

                if(INS_MemoryOperandIsRead(ins, memOp)){
                    read_count++;
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)data_mem_count, 
                                             IARG_PTR, &(ic._single_data_chunk), 
                                             IARG_PTR, &(ic._mult_data_chunk), IARG_MEMORYOP_EA, memOp, 
                                             IARG_ADDRINT, size, IARG_END);

                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT32, cnt, IARG_PTR, &(ic._load), IARG_END);
                }
                if(INS_MemoryOperandIsWritten(ins, memOp)){
                    write_count++;
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)data_mem_count, 
                                             IARG_PTR, &(ic._single_data_chunk), 
                                             IARG_PTR, &(ic._mult_data_chunk), IARG_MEMORYOP_EA, memOp, 
                                             IARG_ADDRINT, size, IARG_END);

                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_access, IARG_UINT32, cnt, IARG_PTR, &(ic._store), IARG_END);
                }
            }
            
            INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
            INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)instr_analysis_predicated, IARG_UINT32, memOperands, 
                                         IARG_UINT32, read_count, IARG_UINT32, write_count, IARG_ADDRINT, mem_size_sum, 
                                         IARG_ADDRINT, max_mem_disp, IARG_ADDRINT, min_mem_disp, IARG_END);
            
        }


        UINT32* ptr = &(ic._others);
        
        if(INS_Category(ins) == XED_CATEGORY_NOP){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_nop), IARG_END);
            ptr = &(ic._nop);
        }
        else if(INS_Category(ins) == XED_CATEGORY_CALL){
            if(INS_IsDirectCall(ins)) {
                //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_dir_call), IARG_END);
                ptr = &(ic._dir_call);
            }
            else {
                //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_indir_call), IARG_END);
                ptr = &(ic._indir_call);
            }
        }
        else if(INS_Category(ins) == XED_CATEGORY_RET){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_ret), IARG_END);
            ptr = &(ic._ret);
        }
        else if(INS_Category(ins) == XED_CATEGORY_UNCOND_BR){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_uncond_br), IARG_END);
            ptr = &(ic._uncond_br);
        }   
        else if(INS_Category(ins) == XED_CATEGORY_COND_BR){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_br), IARG_END);
            ptr = &(ic._cond_br);
        }
        else if(INS_Category(ins) == XED_CATEGORY_LOGICAL){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_logic_op), IARG_END);
            ptr = &(ic._logic_op);
        }
        else if((INS_Category(ins) == XED_CATEGORY_ROTATE) || (INS_Category(ins) == XED_CATEGORY_SHIFT)){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_rot_sht), IARG_END);
            ptr = &(ic._rot_sht);
        }
        else if(INS_Category(ins) == XED_CATEGORY_FLAGOP){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_flag_op), IARG_END);
            ptr = &(ic._flag_op);
        }
        else if((INS_Category(ins) == XED_CATEGORY_AVX) || (INS_Category(ins) == XED_CATEGORY_AVX2) || (INS_Category(ins) == XED_CATEGORY_AVX2GATHER) || (INS_Category(ins) == XED_CATEGORY_AVX512)){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_vect_ins), IARG_END);
            ptr = &(ic._vect_ins);
        }
        else if(INS_Category(ins) == XED_CATEGORY_CMOV){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_cond_mov), IARG_END);
            ptr = &(ic._cond_mov);
        } 
        else if((INS_Category(ins) == XED_CATEGORY_MMX) || (INS_Category(ins) == XED_CATEGORY_SSE)){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_mmx_sse), IARG_END);
            ptr = &(ic._mmx_sse);
        }
        else if(INS_Category(ins) == XED_CATEGORY_SYSCALL){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_syscalls), IARG_END);
            ptr = &(ic._syscalls);    
        }
        else if(INS_Category(ins) == XED_CATEGORY_X87_ALU){
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_fp_ins), IARG_END);
            ptr = &(ic._fp_ins);
        }
        //else {
            //INS_InsertPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, &(ic->_others), IARG_END);
            //ptr = &(ic->_others);
        //}
        
        //cerr << "End of inline Instruction_Count" << '\n';
        INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)fast_forward_check, IARG_END);
        INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)do_cnt, IARG_PTR, ptr, IARG_END);
        //cerr << "End 2 of inline Instruction_Count" << '\n';
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_cnt, IARG_END);
        //cerr << "Extreme end of inline" << endl;
    }
}


//Instrumentation Function
VOID Trace(TRACE trace, VOID* v){
    //cerr << "ic: " << icnt << endl;
    //cerr << "Inside Instruction function" << endl;
    for(BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)){
        BBL_InsertIfCall(bbl, IPOINT_BEFORE, (AFUNPTR)terminate_check, IARG_END);
        BBL_InsertThenCall(bbl, IPOINT_BEFORE, (AFUNPTR)exit_routine, IARG_END);
        
        Instruction_Count(bbl);   
    }
   
    //INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_cnt, IARG_END);
    //cerr << "Ending Instruction function" << endl;
}

//Fini Function, Although it will not be used since we will terminate using exit_routine.
VOID Fini(INT32 code, VOID* v){
    cerr << "Inside Fini Function\n";
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

	//PIN_InitSymbols();
    outfile = new ofstream(KnobOutputFile.Value().c_str());
    
    //cerr << "Inside pintool main and opened outfile" << '\n';

    //-f is passed in terms of billions
    fast_forward_count = KnobFastForwardCount.Value();
    fast_forward_count *= (UINT64)1000000000;
    
    //cerr << "Fast Forward Count: " << fast_forward_count << endl;
    
    //ic = new inst_cnt;
    //memset(ic, 0x00, sizeof(inst_cnt));

    TRACE_AddInstrumentFunction(Trace, 0);

	PIN_AddFiniFunction(Fini, 0);
	PIN_StartProgram();
	
    return 0;
}
