/*****************************************************************************************[Main.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007,      Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>
#include <zlib.h>
#include <string>
#include <memory>

#include "minisat/utils/System.h"
#include "minisat/utils/ParseUtils.h"
#include "minisat/utils/Options.h"
#include "minisat/core/Dimacs.h"
#include "minisat/core/Solver.h"

#include "minisat/core/QCIRParser.h"

using namespace Minisat;

//=================================================================================================


static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        solver->printStats();
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:

bool hasEnding (std::string const &fullString, std::string const &ending) {
    if (fullString.length() >= ending.length()) {
        return (0 == fullString.compare (fullString.length() - ending.length(), ending.length(), ending));
    } else {
        return false;
    }
}

int main(int argc, char** argv)
{
    try {
        setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in QDIMACS or QCIR.\n");
        setX86FPUPrecision();
        
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        //BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", false);
        //BoolOption   solve  ("MAIN", "solve",  "Completely turn on/off solving after preprocessing.", true);
        //StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", 0, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", 0, IntRange(0, INT32_MAX));
        //BoolOption   strictp("MAIN", "strict", "Validate DIMACS header during parsing.", false);
        BoolOption   dl     ("MAIN", "dl",     "Turn on/off dependency learning.", false);
        IntOption    mode   ("MAIN", "mode",   "Propagation mode (0=Q, 1=QU, 2=LDQ).", 0, IntRange(0, 2));
        BoolOption   cert   ("MAIN", "cert",   "Output partial certificate (assignment of first block).", false);
        BoolOption   qcir   ("MAIN", "qcir",   "Use QCIR parser.", false);

        parseOptions(argc, argv, true);

        
        Solver  S;
        double      initial_time = cpuTime();

        S.use_dependency_learning = dl;
        S.verbosity = verb;
        S.mode = mode;
        
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        sigTerm(SIGINT_exit);
        // if (dl && mode == 2) {
        //     printf("Dependency learning not available in LDQ mode.\n");
        //     exit(1);
        // }

        // Try to set resource limits:
        if (cpu_lim != 0) limitTime(cpu_lim);
        if (mem_lim != 0) limitMemory(mem_lim);

        std::unique_ptr<QCIRParser> qcir_parser;

        if (argc == 2 && (hasEnding(std::string(argv[1]), "qcir") || qcir)) {
            std::string filename_string(argv[1]);
            qcir_parser = std::make_unique<QCIRParser>(filename_string);
            qcir_parser->initSolver(S);
        } else {
            if (argc == 1)
                printf("Reading QDIMACS from standard input... Use '--help' for help.\n");

            gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
            if (in == NULL)
                printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
            
            parse_DIMACS(in, S, (bool) false);
            gzclose(in);
        }

        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

        if (S.verbosity > 0){
            printf("|  Number of variables:  %12d                                            |\n", S.nVars());
            printf("|  Number of clauses:    %12d                                            |\n", S.nClauses()); }
        double parsed_time = cpuTime();
        if (S.verbosity > 0)
            printf("|  Parse time:           %12.2f s                                          |\n", parsed_time - initial_time);
                    //==================================================================================
        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        sigTerm(SIGINT_interrupt);

        if (!S.okay()){
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
                printf("==================================================================================\n");
                printf("Solved by simplification\n");
                S.printStats();
                printf("\n"); }
            printf("UNSATISFIABLE\n");
            exit(20);
        }

        lbool ret = l_Undef;

        vec<Lit> dummy;
        ret = S.solveLimited(dummy);

        if (S.verbosity > 0){
            S.printStats();
            printf("\n"); }
        printf(ret == l_True ? "SATISFIABLE\n" : ret == l_False ? "UNSATISFIABLE\n" : "INDETERMINATE\n");
        if (cert) {
            vec<Lit> partial_certificate;
            S.getPartialCertificate(partial_certificate);
            std::cout << "V";
            for (int i = 0; i < partial_certificate.size(); i++) {
                auto l = partial_certificate[i];
                std::cout << " ";
                if (qcir_parser) {
                    std::string name = qcir_parser->getOriginalName(var(l));
                    std::cout << (sign(l) ? "-": "") << name;
                } else {
                    std::cout << (sign(l) ? "-": "") << var(l);
                }
            }
            std::cout << " 0" << std::endl;
        }

#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
        printf("==================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
