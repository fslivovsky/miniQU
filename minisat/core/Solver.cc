/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include "minisat/mtl/Alg.h"
#include "minisat/mtl/Sort.h"
#include "minisat/utils/System.h"
#include "minisat/core/Solver.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));


//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :

    // Parameters (user settable):
    //
    verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , min_learnts_lim  (opt_min_learnts_lim)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), num_clauses(0), num_learnts(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

//  , watches {OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca)), OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca))}
  , order_heap         (VarOrderLt(activity))
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , next_var           (0)
  , max_alias          (-1)
  , dqhead             (0)
  , use_dependency_learning (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{
    watches[0] = new OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca));
    watches[1] = new OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca));
}


Solver::~Solver()
{
    delete watches[0];
    delete watches[1];
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(Var alias, lbool upol, bool dvar)
{
    Var v;
    /*if (free_vars.size() > 0){
        v = free_vars.last();
        free_vars.pop();
    }else*/
    max_alias = (alias > max_alias) ? alias : max_alias;
    v = next_var++;
    variable_names.push(alias);
    alias_to_internal.insert(alias, v);
    variable_type.push(true);
    variable_depth.push(0);
    in_term.push(false);
    dependency_watched_variables.reserve(v);
    dependencies.reserve(v);
    watches[0]->init(mkLit(v, false));
    watches[0]->init(mkLit(v, true ));
    watches[1]->init(mkLit(v, false));
    watches[1]->init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .insert(v, 0);
    polarity .insert(v, true);
    user_pol .insert(v, upol);
    decision .reserve(v);
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


// Note: at the moment, only unassigned variable will be released (this is to avoid duplicate
// releases of the same variable).
void Solver::releaseVar(Lit l)
{
    if (value(l) == l_Undef){
        addClause(l);
        released_vars.push(var(l));
    }
}

void Solver::setVarType(Var x, bool is_existential, int depth) {
    variable_type[x] = is_existential;
    variable_depth[x] = depth;
}


bool Solver::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    for (int i = 0; i < ps.size(); i++) {
        ps[i] = mkLit(alias_to_internal[var(ps[i])], sign(ps[i]));
    }

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        constraint_type.insert(cr, Clauses);
        if (ps.size() == 1){
            p = ps[0];
            bool ct;
            if (variable_type[var(p)]) {
                uncheckedEnqueue(ps[0], cr);
                return ok = (propagate(ct) == CRef_Undef);
            } else {
                return ok = false;
            }
        } else { // ps.size > 1
            attachClause(cr);
        }
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    auto ct = constraint_type[cr];
    assert(c.size() > 1);
    (*watches[ct])[ct == Terms ? c[0] : ~c[0]].push(Watcher(cr, c[1]));
    (*watches[ct])[ct == Terms ? c[1] : ~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) num_learnts++, learnts_literals += c.size();
    else            num_clauses++, clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict){
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    auto ct = constraint_type[cr];
    
    // Strict or lazy detaching:
    if (strict){
        remove((*watches[ct])[ct == Terms ? c[0] : ~c[0]], Watcher(cr, c[1]));
        remove((*watches[ct])[ct == Terms ? c[1] : ~c[1]], Watcher(cr, c[0]));
    }else{
        watches[ct]->smudge(ct == Terms ? c[0] : ~c[0]);
        watches[ct]->smudge(ct == Terms ? c[1] : ~c[1]);
    }

    if (c.learnt()) num_learnts--, learnts_literals -= c.size();
    else            num_clauses--, clauses_literals -= c.size();
}


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    if (c.size() > 1)
        detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level_to) {
    if (decisionLevel() > level_to){
        for (int c = trail.size()-1; c >= trail_lim[level_to]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (!use_dependency_learning) {
                quantifier_blocks_unassigned[variable_depth[x]]++;
            }
            if (phase_saving > 1 || (phase_saving == 1 && c > trail_lim.last()))
                polarity[x] = sign(trail[c]);
            if (!use_dependency_learning || dependencies[x].size() == 0 || (assigns[dependencies[x][0]] != l_Undef && level(dependencies[x][0]) <= level_to)) {
                insertVarOrder(x); 
            }
        }
        qhead = trail_lim[level_to];
        dqhead = (dqhead < trail_lim[level_to]) ? dqhead : trail_lim[level_to];
        trail.shrink(trail.size() - trail_lim[level_to]);
        trail_lim.shrink(trail_lim.size() - level_to);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    if (!use_dependency_learning) {
        updateDecisionVars();
    } else {
        updateDependencyWatchers();
    }
    Var next = var_Undef;

    // Random decision:
    /*if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; } */

    // Activity based decision:

    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        } else {
            next = order_heap.removeMin();
            if (!isEligibleDecision(next)) {
                next = var_Undef;
                if (!use_dependency_learning) {
                    quantifier_blocks_decision_overflow[variable_depth[next]].push(next);
                }
            }
        }

    // Choose polarity based on different polarity modes (global or per-variable):
    if (next == var_Undef)
        return lit_Undef;
    else if (user_pol[next] != l_Undef)
        return mkLit(next, user_pol[next] == l_True);
    else if (rnd_pol)
        return mkLit(next, drand(random_seed) < 0.5);
    else
        return mkLit(next, polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, bool& learn_dependency, bool primary_type)
{
    learn_dependency = false;
    int pathC = 0;
    Lit p     = lit_Undef;
    Lit first = ca[confl][0];

    bool other_type = !primary_type;
    if (assigns[var(first)] == l_Undef) {
        assert(variable_type[var(first)] == other_type);
        uncheckedEnqueue(first, CRef_Undef);
    }
    
    vec<Lit> other_type_literals;

#ifndef NDEBUG
    printf("Conflict %s: ", primary_type ? "clause" : "term");
    printClause(confl);
    printTrail();
#endif

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index = trail.size() - 1;

    int max_primary_dl = 0;
    Clause& cc = ca[confl];
    for (int i = 0; i < cc.size(); i++) {
        Var v = var(cc[i]);
        if (variable_type[v] == primary_type && level(v) > max_primary_dl) {
            max_primary_dl = level(v);
        }
    }

    do {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && variable_type[var(q)] == primary_type && level(var(q)) > 0) {
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= max_primary_dl)
                    pathC++;
                else
                    out_learnt.push(q);
            } else if (!seen[var(q)] && variable_type[var(q)] == other_type) {
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                other_type_literals.push(q);
            }
        }
        
        // Select next clause to look at:
        while (index >= 0 && (!seen[var(trail[index])] || variable_type[var(trail[index])] == other_type)) {
            index--;
        }
        if (index < 0) {
            // Primary constraint empty, bail.
            out_learnt.clear();
            break;
        }
        index--;
        p     = trail[index + 1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    } while (pathC > 0);

    int i = 0;
    int j = 0;
    if (out_learnt.size()) {
        out_learnt[0] = primary_type ? ~p : p;

        // Simplify conflict clause:
        //
        out_learnt.copyTo(analyze_toclear);
        if (ccmin_mode == 2){
            for (i = j = 1; i < out_learnt.size(); i++)
                if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i]))
                    out_learnt[j++] = out_learnt[i];
            
        }else if (ccmin_mode == 1){
            for (i = j = 1; i < out_learnt.size(); i++){
                Var x = var(out_learnt[i]);

                if (reason(x) == CRef_Undef)
                    out_learnt[j++] = out_learnt[i];
                else{
                    Clause& c = ca[reason(var(out_learnt[i]))];
                    for (int k = 1; k < c.size(); k++)
                        if (!seen[var(c[k])] && level(var(c[k])) > 0){
                            out_learnt[j++] = out_learnt[i];
                            break; }
                }
            }
        }else
            i = j = out_learnt.size();
    }

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;   
    for (int j = 0; j < other_type_literals.size(); j++) seen[var(other_type_literals[j])] = 0; // ('seen[]' is now cleared)

    #ifndef NDEBUG
        printf("MiniSAT primary %s: ", primary_type ? "clause" : "term");
        printClause(out_learnt);
        printf("Other literals: ");
        printClause(other_type_literals);
    #endif
    
    // Begin QBF-specific conflict analysis.

    index   = trail.size() - 1;

    Var max_dl_var = var_Undef;
    Var rightmost_primary = var_Undef;

    vec<int> decision_level_counts(decisionLevel() + 1);

    for (i = 0; i < out_learnt.size(); i++) {
        Var v = var(out_learnt[i]);
        seen[v] = 1;
        decision_level_counts[level(v)]++;
        if (variable_type[v] == primary_type && (rightmost_primary == var_Undef || rightmost_primary < v)) {
            rightmost_primary = v;
        }
    }
    if (rightmost_primary != var_Undef) {
        for (i = 0; i < other_type_literals.size(); i++) {
            Var v = var(other_type_literals[i]);
            if (v <= rightmost_primary) {
                seen[v] = 1;
                decision_level_counts[level(v)]++;
            }
        }
        // Search for variable of maximal decision level.
        while (index >= 0 && !seen[var(trail[index--])]);
        index++;
        max_dl_var = (!seen[var(trail[index])]) ? var_Undef : var(trail[index]);
    }

    // While the clause is not asserting, resolve out the rightmost existential literal.
    // TODO: Below - variable_type[max_dl_var]
    while (rightmost_primary != var_Undef && (/*(variable_depth[rightmost_primary] == quantifier_blocks.size() - 1) ||*/ variable_type[max_dl_var] == other_type || level(max_dl_var) == 0 || decision_level_counts[level(max_dl_var)] > 1)) {
#ifndef NDEBUG
        printf("Current %s: ", primary_type ? "clause" : "term");
        printSeen(rightmost_primary);
        printf("Rightmost var: %d\n", variable_names[rightmost_primary]);
        printf("Max DL var: %d\n", variable_names[max_dl_var]);
#endif
        // If there are multiple primaries at the highest decision level, resolve these out first.
        Var pivot = (variable_type[max_dl_var] == primary_type /*&& (variable_depth[rightmost_primary] < quantifier_blocks.size() - 1)*/) ? max_dl_var : rightmost_primary;
        confl = reason(pivot);
        if (confl == CRef_Undef) {
            assert(use_dependency_learning);
            assert(variable_type[max_dl_var] == other_type);
            learn_dependency = true;
            out_learnt.clear();
            out_learnt.push(mkLit(pivot, false));
            out_learnt.push(mkLit(max_dl_var, false));
            out_btlevel = level(pivot) - 1;
            assert(out_btlevel >= 0);
            for (int v = 0; v <= rightmost_primary; v++) {
                seen[v] = 0;
            }
            return;
        }
#ifndef NDEBUG
        printf("Reason %s: ", primary_type ? "clause" : "term");
        printClause(confl);
#endif
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        seen[pivot] = 0;
        decision_level_counts[level(pivot)]--;

        // Account for new primary variables. Check whether one of them is right of the old rightmost primary variable.
        for (int j = 1; j < c.size(); j++) {
            Var v = var(c[j]);
            if (variable_type[v] == primary_type && !seen[v]) {
                seen[v] = 1;
                varBumpActivity(v);
                decision_level_counts[level(v)]++;
                if (rightmost_primary < v) {
                    rightmost_primary = v;
                }
            }
        }
        // If no new rightmost primary was found, search from the old rightmost primary, reducing along the way.
        if (!seen[rightmost_primary]) {
            for (; rightmost_primary >= 0 && (!seen[rightmost_primary] || variable_type[rightmost_primary] == other_type); rightmost_primary--) {
                if (seen[rightmost_primary]) {
                    // Universal variable, reduce.
                    assert(variable_type[rightmost_primary] == other_type);
                    seen[rightmost_primary] = 0;
                    decision_level_counts[level(rightmost_primary)]--;
                }
            }
        }
        // Add blocked universal variables from reason clause.
        if (rightmost_primary != var_Undef) {
            for (int j = 1; j < c.size(); j++) {
                Var v = var(c[j]);
                if (!seen[v] && variable_type[v] == other_type && v < rightmost_primary) {
                    seen[v] = 1;
                    varBumpActivity(v);
                    decision_level_counts[level(v)]++;
                }
            }
        }
        // Search for variable of maximal decision level (including the unassigned universal variable).
        while (index >= 0 && !seen[var(trail[index--])]);
        index++;
        max_dl_var = (!seen[var(trail[index])]) ? var_Undef : var(trail[index]);
    }
    // The clause represented in "seen" is empty or asserting, translate back to vector.
    out_learnt.clear();
    if (rightmost_primary != var_Undef) {
        // Push asserting literal first.
        seen[max_dl_var] = 0;
        out_learnt.push(mkLit(max_dl_var, primary_type ^ toInt(value(max_dl_var))));
        for (int v = 0; v <= rightmost_primary; v++) {
            if (seen[v]) {
                out_learnt.push(mkLit(v, primary_type ^ toInt(value(v))));
                seen[v] = 0;
            }
        }
    }
#ifndef NDEBUG
    printf("Learned %s: ", primary_type ? "clause" : "term");
    printClause(out_learnt);
#endif

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else if (out_learnt.size() > 0) {
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }
}


// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p)
{
    enum { seen_undef = 0, seen_source = 1, seen_removable = 2, seen_failed = 3 };
    assert(seen[var(p)] == seen_undef || seen[var(p)] == seen_source);
    assert(reason(var(p)) != CRef_Undef);

    Clause*               c     = &ca[reason(var(p))];
    vec<ShrinkStackElem>& stack = analyze_stack;
    stack.clear();

    for (uint32_t i = 1; ; i++){
        if (i < (uint32_t)c->size()){
            // Checking 'p'-parents 'l':
            Lit l = (*c)[i];
            
            // Variable at level 0 or previously removable:
            if (level(var(l)) == 0 || seen[var(l)] == seen_source || seen[var(l)] == seen_removable){
                continue; }
            
            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || seen[var(l)] == seen_failed){
                stack.push(ShrinkStackElem(0, p));
                for (int i = 0; i < stack.size(); i++)
                    if (seen[var(stack[i].l)] == seen_undef){
                        seen[var(stack[i].l)] = seen_failed;
                        analyze_toclear.push(stack[i].l);
                    }
                    
                return false;
            }

            // Recursively check 'l':
            stack.push(ShrinkStackElem(i, p));
            i  = 0;
            p  = l;
            c  = &ca[reason(var(p))];
        }else{
            // Finished with current element 'p' and reason 'c':
            if (seen[var(p)] == seen_undef){
                seen[var(p)] = seen_removable;
                analyze_toclear.push(p);
            }

            // Terminate with success if stack is empty:
            if (stack.size() == 0) break;
            
            // Continue with top element on stack:
            i  = stack.last().i;
            p  = stack.last().l;
            c  = &ca[reason(var(p))];

            stack.pop();
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, LSet& out_conflict)
{
    out_conflict.clear();
    out_conflict.insert(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.insert(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
    quantifier_blocks_unassigned[variable_depth[var(p)]]--;
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate(bool& ct)
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        num_props++;
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        
        for (auto ct_ : { Clauses, Terms } ) {
            lbool l_disabling = (ct_ == Clauses) ? l_True : l_False;
            lbool l_vanishing = (ct_ == Clauses) ? l_False : l_True;

            vec<Watcher>&  ws  = watches[ct_]->lookup(p);
            Watcher        *i, *j, *end;

            for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if (value(blocker) == l_disabling){
                    *j++ = *i++; continue; }

                // Make sure the false literal is data[1]:
                CRef     cr        = i->cref;
                Clause&  c         = ca[cr];
                Lit      false_lit = (ct_ == Clauses) ? ~p : p;
                if (c[0] == false_lit)
                    c[0] = c[1], c[1] = false_lit;
                assert(c[1] == false_lit);
                i++;

                // If 0th watch is true, then clause is already satisfied.
                Lit     first = c[0];
                Watcher w     = Watcher(cr, first);
                if (first != blocker && value(first) == l_disabling){
                    *j++ = w; continue; }

                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_vanishing){
                        c[1] = c[k]; c[k] = false_lit;
                        (*watches[ct_])[(ct_ == Clauses) ? ~c[1] : c[1]].push(w);
                        goto NextClause; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if (value(first) == l_vanishing || variable_type[var(first)] == ct_){
                    ct = ct_;
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                } else {
                    uncheckedEnqueue(ct_ == Clauses ? first : ~first, cr);
                }

            NextClause:;
            }
            ws.shrink(i - j);
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else{
            // Trim clause:
            assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) == l_False){
                    c[k--] = c[c.size()-1];
                    c.pop();
                }
            cs[j++] = cs[i];
        }
    }
    cs.shrink(i - j);
}


void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);
    bool ct;
    if (!ok || propagate(ct) != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied){       // Can be turned off.
        removeSatisfied(clauses);

        // TODO: what todo in if 'remove_satisfied' is false?

        // Remove all released variables from the trail:
        for (int i = 0; i < released_vars.size(); i++){
            assert(seen[released_vars[i]] == 0);
            seen[released_vars[i]] = 1;
        }

        int i, j;
        for (i = j = 0; i < trail.size(); i++)
            if (seen[var(trail[i])] == 0)
                trail[j++] = trail[i];
        trail.shrink(i - j);
        //printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
        qhead = trail.size();

        for (int i = 0; i < released_vars.size(); i++)
            seen[released_vars[i]] = 0;

        // Released variables are now ready to be reused:
        append(released_vars, free_vars);
        released_vars.clear();
    }
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    bool        ct;
    bool        learn_dependency = false;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        CRef confl = propagate(ct);
        if (confl != CRef_Undef){
            // CONFLICT
            conflict: // goto label
        
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return (ct == Clauses) ? l_False : l_True;

            if (ct == Terms && ca[confl].size() == 0) return l_True;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, learn_dependency, !ct);
            if (learnt_clause.size() == 0) return (ct == Clauses) ? l_False : l_True;
            if (learn_dependency) {
                assert(learnt_clause.size() == 2);
                Var x = var(learnt_clause[0]);
                Var y = var(learnt_clause[1]);
                dependencies[x].push(y);
                dependencies[x].last() = dependencies[x][0];
                dependencies[x][0] = y;
                dependency_watched_variables[y].push(x);
                cancelUntil(backtrack_level);
                #ifndef NDEBUG
                printf("Learned dependency of %d on %d.\n", variable_names[x], variable_names[y]);
                #endif
                if (order_heap.inHeap(x)) {
                    order_heap.remove(x);
                }
                if (dependencies[x].size() > 1) { // Remove x from list of variables watched by the old watcher.
                    Var old_watcher = dependencies[x].last();
                    auto &watched = dependency_watched_variables[old_watcher];
                    int i;
                    for (i = 0; i < watched.size() && watched[i] != x; i++);
                    assert(i < watched.size());
                    watched[i] = watched.last();
                    watched.shrink(1);
                }
            } else {
                cancelUntil(backtrack_level);
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                constraint_type.insert(cr, ct);

                if (learnt_clause.size() > 1) {
                    attachClause(cr);
                    claBumpActivity(ca[cr]);
                }
                uncheckedEnqueue((ct == Clauses) ? learnt_clause[0] : ~learnt_clause[0], cr);


                varDecayActivity();
                claDecayActivity();

                if (--learntsize_adjust_cnt == 0){
                    learntsize_adjust_confl *= learntsize_adjust_inc;
                    learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                    max_learnts             *= learntsize_inc;

                    if (verbosity >= 1)
                        printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                            (int)conflicts, 
                            (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                            (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
                }
            }

        }else{
            // NO CONFLICT
            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts) || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            // if (decisionLevel() == 0 && !simplify())
            //    return l_False;

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            /*while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }*/

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef) {
                    // Model found.
                    getInitialTerm();
                    confl = initial_term_ref;
                    ct = Terms;
                #ifndef NDEBUG
                    printf("Initial term found. \n");
                #endif
                    goto conflict;
                }
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;

    max_learnts = nClauses() * learntsize_factor;
    if (max_learnts < min_learnts_lim)
        max_learnts = min_learnts_lim;

    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    allocInitialTerm();
    //status = addInitialTerms();

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}


bool Solver::implies(const vec<Lit>& assumps, vec<Lit>& out)
{
    trail_lim.push(trail.size());
    for (int i = 0; i < assumps.size(); i++){
        Lit a = assumps[i];

        if (value(a) == l_False){
            cancelUntil(0);
            return false;
        }else if (value(a) == l_Undef)
            uncheckedEnqueue(a);
    }

    unsigned trail_before = trail.size();
    bool     ret          = true;
    bool ct;
    if (propagate(ct) == CRef_Undef){
        out.clear();
        for (int j = trail_before; j < trail.size(); j++)
            out.push(trail[j]);
    }else
        ret = false;
    
    cancelUntil(0);
    return ret;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote DIMACS with %d variables and %d clauses.\n", max, cnt);
}


void Solver::printStats() const
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("restarts              : %"PRIu64"\n", starts);
    printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
    if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
    printf("CPU time              : %g s\n", cpu_time);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    watches[Clauses]->cleanAll();
    watches[Terms]  ->cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            for (auto ct: {Clauses, Terms}) {
                vec<Watcher>& ws = (*watches[ct])[p];
                for (int j = 0; j < ws.size(); j++)
                    ca.reloc(ws[j].cref, to);
            }
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
        // 'dangling' reasons here. It is safe and does not hurt.
        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)]))){
            assert(!isRemoved(reason(v)));
            ca.reloc(vardata[v].reason, to);
        }
    }

    // New constraint type map.
    CMap<bool> constraint_type_;

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            auto ct = constraint_type[learnts[i]];
            ca.reloc(learnts[i], to);
            constraint_type_.insert(learnts[i], ct);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            ca.reloc(clauses[i], to);
            constraint_type_.insert(clauses[i], Clauses);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);

    // Initial term:
    Clause& initial_term = ca[initial_term_ref];
    initial_term.setSize(nVars());
    ca.reloc(initial_term_ref, to);

    // All terms:
    //
    for (i = j = 0; i < terms.size(); i++)
        if (!isRemoved(terms[i])){
            ca.reloc(terms[i], to);
            constraint_type_.insert(terms[i], Terms);
            terms[j++] = terms[i];
        }
    terms.shrink(i - j);

    constraint_type_.moveTo(constraint_type);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

bool Solver::isEligibleDecision(Var x) const {
    if (!use_dependency_learning) {
        for (int i = 0; i < variable_depth[x]; i++) {
            if (quantifier_blocks_type[i] != variable_type[x] && quantifier_blocks_unassigned[i] > 0) {
                return false;
            }
        }
        return true;
    } else {
        return dependencies[x].size() == 0 || value(dependencies[x][0]) != l_Undef;
    }
}

void Solver::updateDecisionVars() {
    for (int quantifier_type = 0; quantifier_type < 2; quantifier_type++) {
        for (int i = 0; i < quantifier_blocks.size(); i++) {
            if (quantifier_blocks_type[i] == quantifier_type) {
                // All quantifier blocks of different type and lower depth have been assigned.
                for (int j = 0; j < quantifier_blocks_decision_overflow[i].size(); j++) {
                    Var v = quantifier_blocks_decision_overflow[i][j];
                    insertVarOrder(v);
                }
                quantifier_blocks_decision_overflow[i].clear();
            } else if (quantifier_blocks_unassigned[i]) {
                break;
            }
        }
    }
}

void Solver::getInitialTerm() {
    Clause& initial_term = ca[initial_term_ref];
    int initial_term_size = 0;
    for (int i = 0; i < clauses.size(); i++) {
        CRef cr = clauses[i];
        Clause& c = ca[cr];
        int j;
        for (j = 0; j < c.size() && (value(c[j]) != l_True || !in_term[var(c[j])]); j++);
        if (j == c.size())
            for (j = 0; j < c.size() && value(c[j]) != l_True; j++);
        assert(j < c.size());
        Lit p = c[j];
        if (!in_term[var(p)]) {
            initial_term[initial_term_size++] = p;
            in_term[var(p)] = true;
        }
    }
    // Clean up "in_term" vector.
    for (int i = 0; i < initial_term_size; i++) {
        Lit p = initial_term[i];
        in_term[var(p)] = false;
    }
    Var max_universal = var_Undef;
    for (int i = 0; i < initial_term_size; i++) {
        Var v = var(initial_term[i]);
        if (!variable_type[v] && (max_universal < v || max_universal == var_Undef)) {
            max_universal = v;
        }
    }
    #ifndef NDEBUG
    printf("Unreduced initial term: ");
    initial_term.setSize(initial_term_size);
    printClause(initial_term_ref);
    #endif
    int i, j;
    for (i = j = 0; i < initial_term_size; i++) {
        Var v = var(initial_term[i]);
        if (v <= max_universal) {
            initial_term[j++] = initial_term[i];
        } else {
            varBumpActivity(v);
        }
    }
    initial_term.setSize(j);
}

void Solver::printClause(CRef cr) const {
    const Clause& c = ca[cr];
    for (int i = 0; i < c.size(); i++) {
        Lit p = c[i];
        Var v = variable_names[var(p)];
        printf("%d ", sign(p) ? -v : v);
    }
    printf("\n");
}

void Solver::printClause(const vec<Lit>& literals) const {
    for (int i = 0; i < literals.size(); i++) {
        Lit p = literals[i];
        Var v = variable_names[var(p)];
        printf("%d ", sign(p) ? -v : v);
    }
    printf("\n");
}

void Solver::printTrail() const {
    printf("Trail: ");
    for (int i = 0; i < trail.size(); i++) {
        Lit p = trail[i];
        Var v = variable_names[var(p)];
        printf("%c%d@%d ", variable_type[var(p)] ? 'E' : 'A', sign(p) ? -v : v, level(var(p)));
    }
    printf("\n");
}

void Solver::printSeen(Var rightmost) const {
    for (int v = 0; v <= rightmost; v++) {
        if (seen[v]) {
            printf("%d ", variable_names[v]);
        }
    }
    printf("\n");
}

void Solver::updateDependencyWatchers() {
    while (dqhead < trail.size()) {
        Var v = var(trail[dqhead++]);
        vec<Var>& watched = dependency_watched_variables[v];
        int i, j;
        for (i = j = 0; i < watched.size(); i++) {
            Var w = watched[i];
            // Find a new watcher for w.
            int k;
            assert(dependencies[w][0] == v);
            for (k = 1; k < dependencies[w].size() && value(dependencies[w][k]) != l_Undef; k++);
            if (k < dependencies[w].size()) {
                // New watcher found. Put at at index 0 of dependency vec.
                Var y = dependencies[w][k];
                dependencies[w][k] = dependencies[w][0];
                dependencies[w][0] = y;
                dependency_watched_variables[y].push(w);
            } else {
                // No new watcher found. Insert w into decision queue.
                insertVarOrder(w);
                watched[j++] = w;
            }
        }
        watched.shrink(i - j);
    }
}

void Solver::allocInitialTerm() {
    vec<Lit> all_variables(nVars());
    initial_term_ref = ca.alloc(all_variables, false);
}

lbool Solver::addTerm(const vec<Lit>& term) {
    CRef cr = ca.alloc(term, false);
#ifndef NDEBUG
    printf("Adding term: ");
    printClause(term);
#endif
    terms.push(cr);
    constraint_type.insert(cr, Terms);
    if (term.size() == 1){
        Lit p = term[0];
        bool ct;
        if (!variable_type[var(p)]) {
            uncheckedEnqueue(~p, cr);
            if (propagate(ct) != CRef_Undef) {
                return lbool(ct);
            }
        }
    } else {
        attachClause(cr);
    }
    return l_Undef;
}

lbool Solver::addInitialTerms() {
    vec<Var> tseitin_variables;
    for (int i = 0; i < clauses.size(); i++) {
        Var v = newVar(++max_alias, l_Undef, false);
        setVarType(v, false, quantifier_blocks.size());
        tseitin_variables.push(v);
    }
    addQuantifierBlock(tseitin_variables, false);
    vec<Lit> term;
    for (int i = 0; i < clauses.size(); i++) {
        assert(!term.size());
        term.push(mkLit(tseitin_variables[i], true));
        Clause& c = ca[clauses[i]];
        for (int j = 0; j < c.size(); j++) {
            Lit p = c[j];
            term.push(p);
            addTerm(term);
            term.pop();
        }
        term.pop();
    }
    for (int i = 0; i < tseitin_variables.size(); i++) {
        term.push(mkLit(tseitin_variables[i], false));
    }
    auto val = addTerm(term);
    if (val != l_Undef) {
        assert(val == l_True);
        return val;
    } else {
        // Propagate decision level 0 again.
        bool ct;
        qhead = 0;
        if (propagate(ct) != CRef_Undef) {
            return lbool(ct);
        }
        return l_Undef;
    }
}
