/****************************************************************************************[Dimacs.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef Minisat_Dimacs_h
#define Minisat_Dimacs_h

#include <stdio.h>

#include "minisat/utils/ParseUtils.h"
#include "minisat/core/SolverTypes.h"

namespace Minisat {

//=================================================================================================
// DIMACS Parser:

template<class B, class Solver>
static void readClause(B& in, Solver& S, vec<Lit>& lits) {
    int     parsed_lit, var;
    lits.clear();
    for (;;){
        parsed_lit = parseInt(in);
        if (parsed_lit == 0) break;
        var = abs(parsed_lit);
        lits.push( (parsed_lit > 0) ? mkLit(var) : ~mkLit(var) );
    }
    S.addClause_(lits);
}

template<class B, class Solver>
static void readQuantifierBlock(B& in, Solver& S, bool is_existential, int depth) {
    ++in;
    skipWhitespace(in);
    Var parsed_var;
    vec<Var> variables;
    for (;;) {
        parsed_var = parseInt(in);
        if (parsed_var == 0) break;
        Var internal_variable = S.newVar(parsed_var);
        S.setVarType(internal_variable, is_existential, depth);
        variables.push(internal_variable);
        //printf("Variable ex. %c at depth %i.\n", is_existential ? 'e' : 'a', depth);
    }
    S.addQuantifierBlock(variables, is_existential);
    //printf("Quantifier block ex. %c with %i variables.\n", is_existential ? 'e' : 'a', variables.size());
}

template<class B, class Solver>
static void parse_DIMACS_main(B& in, Solver& S, bool strictp = false) {
    vec<Lit> lits;
    VMap<Var> alias_to_interal;
    int clauses = 0;
    int cnt     = 0;
    int depth   = 0;
    for (;;){
        skipWhitespace(in);
        if (*in == EOF) break;
        else if (*in == 'p'){
            if (eagerMatch(in, "p cnf")){
                int vars = parseInt(in);
                clauses = parseInt(in);
                if (vars < 0 || clauses < 0) {
                    printf("Number of variables and clauses in header must be positive. \n"), exit(3);
                }
            }else{
                printf("PARSE ERROR! Unexpected char: %c\n", *in), exit(3);
            }
        } else if (*in == 'c' || *in == 'p') {
            skipLine(in);
        } else if (*in == 'a') {
            readQuantifierBlock(in, S, false, depth++);
        } else if (*in == 'e') {
            readQuantifierBlock(in, S, true, depth++);
        } else {
            cnt++;
            readClause(in, S, lits); }
    }
    if (strictp && cnt != clauses)
        printf("PARSE ERROR! DIMACS header mismatch: wrong number of clauses\n");
}

// Inserts problem into solver.
//
template<class Solver>
static void parse_DIMACS(gzFile input_stream, Solver& S, bool strictp = false) {
    StreamBuffer in(input_stream);
    parse_DIMACS_main(in, S, strictp); }

//=================================================================================================
}

#endif
