#include "pin.H"
#include <iostream>
#include <fstream>
#include <set>
#include <map>
#include <chrono>
using namespace std;

chrono::time_point<chrono::high_resolution_clock> startTime, endTime;

UINT64 fast_forward_count = 0;	// Should be a command line input to your PIN tool
UINT64 insCount = 0;    // number of dynamically executed instructions
UINT64 bblCount = 0;    // number of dynamically executed basic blocks
UINT64 threadCount = 0; // total number of threads, including main thread
UINT64 num_ins = 0;    
UINT64 num_loads = 0;
UINT64 num_stores = 0;
UINT64 num_nops = 0;
UINT64 num_direct_calls = 0;
UINT64 num_indirect_calls = 0;
UINT64 num_returns = 0;
UINT64 num_uncond_branches = 0;
UINT64 num_cond_branches = 0;
UINT64 num_logical_ops = 0;
UINT64 num_rotate_shifts = 0;
UINT64 num_flag_ops = 0;
UINT64 num_vec_ins = 0;
UINT64 num_cond_moves = 0;
UINT64 num_mmx_sse_ins = 0;
UINT64 num_sys_calls = 0;
UINT64 num_flops = 0;
UINT64 num_others = 0;

set<UINT32> instrAddr;
set<UINT32> dataAddr;
map<UINT32, UINT64> insLength; 
map<UINT32, UINT64> insOp; 
map<UINT32, UINT64> readReg; 
map<UINT32, UINT64> writeReg;
map<UINT32, UINT64> memOp;
map<UINT32, UINT64> memReadOp;
map<UINT32, UINT64> memWriteOp;
UINT32 maxMemBytes = 0;
UINT64 totalMemBytes = 0;
INT32 maxImm = INT32_MIN;
INT32 minImm = INT32_MAX;
INT32 maxDisp = INT32_MIN;
INT32 minDisp = INT32_MAX;

std::ostream *out = &cerr;
UINT64 total_ins = 0;

KNOB<BOOL> KnobCount(KNOB_MODE_WRITEONCE, "pintool", "count", "1", "count instructions, basic blocks and threads in the application");
KNOB<UINT64> KnobFastForward(KNOB_MODE_WRITEONCE, "pintool", "f", "0", "Fast-forward amount");
KNOB<string> KnobOutputFile(KNOB_MODE_WRITEONCE, "pintool", "o", "HW1.out", "specify output file name");

INT32 Usage()
{
    cerr << "This tool prints out the number of dynamically executed " << endl
         << "instructions, basic blocks and threads in the application." << endl
         << endl;

    cerr << KNOB_BASE::StringKnobSummary() << endl;

    return -1;
}

VOID count_insbb(UINT32 x) { insCount += x; }

VOID count_ins() { insCount++; }

VOID count_loads(UINT32 x) {num_loads+=x; }

VOID count_stores(UINT32 x) {num_stores+=x;}

VOID count_nops() {num_nops++;}

VOID count_direct_calls() {num_direct_calls++;}

VOID count_indirect_calls() {num_indirect_calls++;}

VOID count_returns() { num_returns++; }

VOID count_uncond_branches() { num_uncond_branches++; }

VOID count_cond_branches() { num_cond_branches++; }

VOID count_logical_ops() { num_logical_ops++; }

VOID count_rotate_shifts() { num_rotate_shifts++; }

VOID count_flag_ops() { num_flag_ops++; }

VOID count_vec_ins() { num_vec_ins++; }

VOID count_cond_moves() { num_cond_moves++; }

VOID count_mmx_sse_ins() { num_mmx_sse_ins++; }

VOID count_sys_calls() { num_sys_calls++; }

VOID count_flops() { num_flops++; }

VOID count_others() { num_others++; }

ADDRINT Terminate(void) { return (insCount >= fast_forward_count + 1000000000); }

ADDRINT FastForward (void) { return ((insCount >= fast_forward_count) && (insCount < fast_forward_count + 1000000000)); }


VOID ins_footprint(UINT32 startAddr, UINT32 endAddr){
    while(startAddr <= endAddr){
        instrAddr.insert(startAddr);
        startAddr += 32;
    }
}

VOID data_footprint(ADDRINT memAddr, UINT32 memSize){
    UINT32 mAddr = (UINT32) memAddr;
    UINT32 startAddr = (mAddr/32)*32;
    UINT32 endAddr = ((mAddr + memSize)/32)*32;
    while(startAddr <= endAddr){
        dataAddr.insert(startAddr);
        startAddr += 32;
    }
}

VOID ins_distribution(
    UINT32 insSize, 
    UINT32 opCount, 
    UINT32 insReadReg, 
    UINT32 insWriteReg
){
    insLength[insSize]++;
    insOp[opCount]++;
    readReg[insReadReg]++; 
    writeReg[insWriteReg]++;
    
}

VOID mem_distribution(
    UINT32 numRead, 
    UINT32 numWrite,
    UINT32 totalMemSize
){
    memOp[numRead+numWrite]++; 
    memReadOp[numRead]++; 
    memWriteOp[numWrite]++;
    maxMemBytes = max(maxMemBytes, totalMemSize);
    totalMemBytes += totalMemSize;
}

VOID imm_distribution(ADDRINT immValue){
    INT32 imm = (INT32) immValue;
    maxImm = max(maxImm, imm);
    minImm = min(minImm, imm);
}

VOID disp_distribution(ADDRINT dispValue){
    INT32 disp = (INT32) dispValue;
    maxDisp = max(maxDisp, disp);
    minDisp = min(minDisp, disp);
}

void PrintRow(const string &name, UINT64 count){
    double percentage = (total_ins == 0) ? 0.0 : (100.0 * count / total_ins);
    *out << left << setw(30) << name
         << setw(15) << count
         << setw(14) << fixed << setprecision(6) << percentage << "%" << endl;
}

void PrintResults(const string &title, const map<UINT32, UINT64> &data) {
    *out << title << " Results: " << endl;
    for (const auto &entry : data) {
        *out << entry.first << " : " << entry.second << endl;
    }
    *out << endl;
}

void MyExitRoutine() {
    total_ins = num_loads + num_stores + num_nops + num_direct_calls +
                num_indirect_calls + num_returns + num_uncond_branches +
                num_cond_branches + num_logical_ops + num_rotate_shifts +
                num_flag_ops + num_vec_ins + num_cond_moves +
                num_mmx_sse_ins + num_sys_calls + num_flops + num_others;
    
    UINT64 memInsCount = 0;
    for(const auto &entry : memOp){
        if(entry.first > 0) memInsCount += entry.second;
    }
    double avgMemBytes = (memInsCount == 0) ? 0.0 : ((1.0*totalMemBytes) / memInsCount);

    memReadOp[0] = memReadOp[0]-memOp[0];
    memWriteOp[0] = memWriteOp[0]-memOp[0];
    
    *out << "============================================================" << endl;
    *out << "Part A Analysis Results: " << endl;
    *out << "------------------------------------------------------------" << endl;

    *out << "Total Instructions: " << insCount << endl;
    *out << "Total Instructions after fast forward: " << insCount - fast_forward_count << endl;
    *out << "------------------------------------------------------------" << endl;

    // Formatting the table header
    *out << left << setw(30) << "Instruction Type" << setw(15) << "Count" << setw(15) << "Percentage" << endl;
    *out << "------------------------------------------------------------" << endl;

    // Printing each instruction type
    PrintRow("Loads", num_loads);
    PrintRow("Stores", num_stores);
    PrintRow("NOPs", num_nops);
    PrintRow("Direct Calls", num_direct_calls);
    PrintRow("Indirect Calls", num_indirect_calls);
    PrintRow("Returns", num_returns);
    PrintRow("Unconditional Branches", num_uncond_branches);
    PrintRow("Conditional Branches", num_cond_branches);
    PrintRow("Logical Operations", num_logical_ops);
    PrintRow("Rotate & Shift", num_rotate_shifts);
    PrintRow("Flag Operations", num_flag_ops);
    PrintRow("Vector Instructions", num_vec_ins);
    PrintRow("Conditional Moves", num_cond_moves);
    PrintRow("MMX & SSE Instructions", num_mmx_sse_ins);
    PrintRow("System Calls", num_sys_calls);
    PrintRow("Floating-Point", num_flops);
    PrintRow("Others", num_others);

    *out << "============================================================" << endl;

    *out << "Part B Analysis Results: " << endl;
    double cpi = (4.0*(num_loads + num_stores) + total_ins)/(total_ins); 
    *out << "CPI = " << (4.0*(num_loads + num_stores) + total_ins)/(total_ins) << endl;
	
    *out << "Total Runtime: " << (double)insCount * cpi << endl;
    *out << "============================================================" << endl;

    *out << "Part C Analysis Results: " << endl;
    *out << "------------------------------------------------------------" << endl;

    *out << "Instruction Footprint Blocks     = " << instrAddr.size() << endl;
    *out << "Instruction Footprint (in bytes) = " << 32*instrAddr.size() << endl;
    *out << "Data Footprint Blocks            = " << dataAddr.size() << endl;
    *out << "Data Footprint (in bytes)        = " << 32*dataAddr.size() << endl;

    *out << "============================================================" << endl;

    *out << "Part D Analysis Results: " << endl;
    *out << "------------------------------------------------------------" << endl;

    PrintResults("Instruction Size", insLength);
    PrintResults("Memory Instruction Operand", memOp);
    PrintResults("Memory Instruction Read Operand", memReadOp);
    PrintResults("Memory Instruction Write Operand", memWriteOp);
    PrintResults("Instruction Operand", insOp);
    PrintResults("Instruction Register Read Operand", readReg);
    PrintResults("Instruction Register Write Operand", writeReg);
    

    *out << "Maximum number of bytes touched by an instruction : " << maxMemBytes << endl;
    *out << "Average number of bytes touched by an instruction : " << fixed << setprecision(6) << avgMemBytes << endl;
    *out << "Maximum value of immediate : " << maxImm << endl;
    *out << "Minimum value of immediate : " << minImm << endl;
    *out << "Maximum value of displacement used in memory addressing : " << maxDisp << endl;
    *out << "Minimum value of displacement used in memory addressing : " << minDisp << endl;
    endTime = chrono::high_resolution_clock::now();
    chrono::duration<double> elapsed = endTime - startTime;
    *out << "Time taken : " << elapsed.count() << " seconds." << endl;
	exit(0);
}

VOID Trace(TRACE trace, VOID *v)
{
    for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)) {
        BBL_InsertIfCall(bbl, IPOINT_BEFORE, (AFUNPTR) Terminate, IARG_END);
        BBL_InsertThenCall(bbl, IPOINT_BEFORE, MyExitRoutine, IARG_END);
        BBL_InsertCall(bbl, IPOINT_BEFORE, (AFUNPTR)count_insbb, IARG_UINT32, BBL_NumIns(bbl), IARG_END);
        for(INS ins=BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)){
            UINT32 startAddr, endAddr;
            UINT32 insAddr = INS_Address(ins);
            UINT32 insSize = INS_Size(ins);
            startAddr = (insAddr/32)*32;
            endAddr = ((insAddr + insSize)/32)*32;
            INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
            INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_footprint, IARG_UINT32, startAddr, IARG_UINT32, endAddr, IARG_END);

            UINT32 opCount = INS_OperandCount(ins);
            UINT32 insReadReg = INS_MaxNumRRegs(ins);
            UINT32 insWriteReg = INS_MaxNumWRegs(ins);

            UINT32 memOperands = INS_MemoryOperandCount(ins);
            UINT32 numRead = 0, numWrite = 0;
            UINT32 totalMemSize = 0;

            for (UINT32 memOper = 0; memOper < memOperands; memOper++)
            {
                UINT32 memSize = INS_MemoryOperandSize(ins, memOper);
                UINT32 num = 1;
                if (INS_MemoryOperandIsRead(ins, memOper)){
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_loads, IARG_UINT32, num, IARG_END);
                    numRead++;
                }
                if (INS_MemoryOperandIsWritten(ins, memOper)){  
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_stores, IARG_UINT32, num, IARG_END);
                    numWrite++;
                }
                if (INS_OperandIsMemory(ins, memOper)) {
                    ADDRDELTA displacement = INS_OperandMemoryDisplacement(ins, memOper);
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)disp_distribution, IARG_ADDRINT, displacement, IARG_END);
                }
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)data_footprint, IARG_MEMORYOP_EA, memOper, IARG_UINT32, memSize, IARG_END);
                totalMemSize += memSize;
            }

            INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
            INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)ins_distribution, 
                            IARG_UINT32, insSize, 
                            IARG_UINT32, opCount, 
                            IARG_UINT32, insReadReg, 
                            IARG_UINT32, insWriteReg, 
                            IARG_END);

            INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
            INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)mem_distribution,  
                                IARG_UINT32, numRead, 
                                IARG_UINT32, numWrite,
                                IARG_UINT32, totalMemSize,
                                IARG_END);

            if (INS_Category(ins) == XED_CATEGORY_NOP) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_nops, IARG_END);
            }
                
            else if (INS_Category(ins) == XED_CATEGORY_CALL) {
                if (INS_IsDirectCall(ins)) {
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_direct_calls, IARG_END);
                }
                else {
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_indirect_calls, IARG_END);
                }
            }

            else if (INS_Category(ins) == XED_CATEGORY_RET) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_returns, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_UNCOND_BR) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_uncond_branches, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_COND_BR) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_cond_branches, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_LOGICAL) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_logical_ops, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_ROTATE || INS_Category(ins) == XED_CATEGORY_SHIFT) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_rotate_shifts, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_FLAGOP) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_flag_ops, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_AVX || INS_Category(ins) == XED_CATEGORY_AVX2 || 
                INS_Category(ins) == XED_CATEGORY_AVX2GATHER || INS_Category(ins) == XED_CATEGORY_AVX512) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_vec_ins, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_CMOV) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_cond_moves, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_MMX || INS_Category(ins) == XED_CATEGORY_SSE) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_mmx_sse_ins, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_SYSCALL) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_sys_calls, IARG_END);
            }

            else if (INS_Category(ins) == XED_CATEGORY_X87_ALU) {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_flops, IARG_END);
            }

            else {
                INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                INS_InsertThenPredicatedCall(ins, IPOINT_BEFORE, (AFUNPTR)count_others, IARG_END);
            }

            UINT32 operandCount = INS_OperandCount(ins);
            for (UINT32 opIdx = 0; opIdx < operandCount; opIdx++) {
                if (INS_OperandIsImmediate(ins, opIdx)) {
                    INT32 immValue = INS_OperandImmediate(ins, opIdx);
                    INS_InsertIfCall(ins, IPOINT_BEFORE, (AFUNPTR)FastForward, IARG_END);
                    INS_InsertThenCall(ins, IPOINT_BEFORE, (AFUNPTR)imm_distribution, IARG_ADDRINT, immValue,IARG_END);
                }
            }
        }
    }
}


VOID Fini(INT32 code, VOID *v)
{
    MyExitRoutine();
    cout << "This should not be printed :(" << endl;
    
}



int main(int argc, char *argv[])
{   

    startTime = chrono::high_resolution_clock::now();
    if (PIN_Init(argc, argv))
    {
        return Usage();
    }

    string fileName = KnobOutputFile.Value();
    fast_forward_count = KnobFastForward.Value();

    if (!fileName.empty())
    {
        out = new std::ofstream(fileName.c_str());
    }

    if (KnobCount)
    {
        TRACE_AddInstrumentFunction(Trace, 0);

        // Register Instruction to be called to instrument instructions
        // INS_AddInstrumentFunction(Instrumentation, 0);

        // Register function to be called when the application exits
        PIN_AddFiniFunction(Fini, 0);
    }

    cerr << "===============================================" << endl;
    cerr << "Results of instrumenting the given binary:" << endl;
    if (!KnobOutputFile.Value().empty())
    {
        cerr << "See file " << KnobOutputFile.Value() << " for analysis results" << endl;
    }
    cerr << "===============================================" << endl;

    // Start the program, never returns
    PIN_StartProgram();

    return 0;
}
