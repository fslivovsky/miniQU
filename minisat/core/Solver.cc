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
#include <inttypes.h>

#include <algorithm>
#include <iostream>

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
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep, 3=new)", 0, IntRange(0, 3));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_min_learnts_lim   (_cat, "min-learnts", "Minimum learnt clause limit",  0, IntRange(0, INT32_MAX));
static StringOption  opt_trace             (_cat, "trace",       "If given, write trace to this file.");


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
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0), nr_dependencies(0)
  , dec_vars(0), num_clauses(0), num_learnts{0, 0}, clauses_literals(0), learnts_literals{0, 0}, max_literals(0), tot_literals(0)

//  , watches {OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca)), OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca))}
  //, order_heap         (VarOrderLt(activity))
  , ok                 (true)
  , input_status       (l_Undef)
  , cla_inc            (1)
  , var_inc            (1)
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , next_var           (0)
  , dqhead             (0)
  , max_alias          (-1)
  , running_id         (1)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
  , trace              (false)
{
    if (opt_trace) {
        trace = true;
        trace_file.open(opt_trace);
    }
    watches[0] = new OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca));
    watches[1] = new OccLists<Lit, vec<Watcher>, WatcherDeleted, MkIndexLit>(WatcherDeleted(ca));
}


Solver::~Solver()
{
    // delete watches[0];
    // delete watches[1];
    // if (use_dependency_learning) {
    //     delete order_heaps[0];
    // } else {
    //     for (int i = 0; i < quantifier_blocks.size(); i++) {
    //         delete order_heaps[i];
    //     }
    // }
    // delete[] order_heaps;
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
    variable_type.push(true); //push
    variable_depth.push(0);
    in_term.push(false);
    dependency_watched_variables.reserve(v);
    dependencies.reserve(v);
    watches[0]->init(mkLit(v, false));
    watches[0]->init(mkLit(v, true ));
    watches[1]->init(mkLit(v, false));
    watches[1]->init(mkLit(v, true ));
    assigns  .insert(v, l_Undef);
    vardata  .insert(v, mkVarData(CRef_Undef, 0, ConstraintTypes::Clauses));
    activity .insert(v, rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen_at.push(-1);
    seen.push(0);
    removable_if.push(-1);
    if (mode == 2) {
        seen_at.push(-1);
    }
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

    vec<Lit> ps_copy;
    ps.copyTo(ps_copy);
    sort(ps_copy);

    // Remove tautologies
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps_copy.size(); i++) 
        if (ps_copy[i] != ~p) {
            ps_copy[j++] = p = ps_copy[i];
        } else {
            return true;
        }
    ps_copy.shrink(i - j);

    return addClauseInternal(ps_copy);
}

bool Solver::addClauseInternal(const vec<Lit>& ps) {
    vec<Lit> ps_copy;
    ps.copyTo(ps_copy);
    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps_copy);
    Lit p; int i, j;

    #ifndef NDEBUG
    printf("Adding clause: ");
    printClause(ps_copy);
    #endif

    for (i = j = 0, p = lit_Undef; i < ps_copy.size(); i++)
        if (value(ps_copy[i]) == l_True)
            return true;
        else if (value(ps_copy[i]) != l_False && ps_copy[i] != p)
            ps_copy[j++] = p = ps_copy[i];
    ps_copy.shrink(i - j);

    // Check for tautologies.
    for (i = 1; i < ps_copy.size(); i++) {
        if (ps_copy[i] == ~ps_copy[i-1]) {
            return true;
        }
    }

    reduce(ps_copy, true);

    if (ps_copy.size() == 0) {
        input_status = l_False;
        return ok = false;
    }
    else {
        CRef cr = ca.alloc(ps_copy, false);
        clauses.push(cr);
        constraint_type.insert(cr, Clauses);
        if (trace) {
            auto id = running_id++;
            constraint_ID.insert(cr, id);
        }
        //constraint_type[cr] = Clauses;
        if (ps_copy.size() == 1){
            p = ps_copy[0];
            if (variable_type[var(p)]) {
                uncheckedEnqueue(ps_copy[0], cr, ConstraintTypes::Clauses);
                return ok = true;
            } else {
                input_status = l_False;
                return ok = false;
            }
        } else { // ps_copy.size > 1
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
    if (c.learnt()) num_learnts[ct]++, learnts_literals[ct] += c.size();
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

    if (c.learnt()) num_learnts[ct]--, learnts_literals[ct] -= c.size();
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
        if (use_dependency_learning) {
            dqhead = (dqhead < trail_lim[level_to]) ? dqhead : trail_lim[level_to];
        }
        qhead = trail_lim[level_to];
        trail.shrink(trail.size() - trail_lim[level_to]);
        trail_lim.shrink(trail_lim.size() - level_to);
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    int i;
    if (!use_dependency_learning) {
        i = getDecisionBlock();
    } else {
        i = 0;
        updateDependencyWatchers();
    }

    if (i == quantifier_blocks.size()) {
        return lit_Undef;
    }

    Var next = var_Undef;

    // Random decision:
    bool make_random_decision = random_var_freq > 0 && (drand(random_seed) < random_var_freq && !order_heaps[i]->empty());
    rnd_decisions += make_random_decision;

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heaps[i]->empty()){
            next = var_Undef;
            break;
        } else {
            if (make_random_decision) {
                next = (*order_heaps[i])[irand(random_seed, order_heaps[i]->size())];
            } else {
                next = order_heaps[i]->removeMin();
            }
            if (!isEligibleDecision(next)) {
                next = var_Undef;
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
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, bool& learn_dependency, bool& ct)
{
    Var r = var_Undef;

    analyzeStart:

    learn_dependency = false;
    bool primary_type = (ct == ConstraintTypes::Clauses);
    bool other_type = !primary_type;
    vec<uint64_t> premise_ids;

    if (trace)
        premise_ids.push(constraint_ID[confl]);

    #ifndef NDEBUG
    uint64_t id;
    assert(!trace || (constraint_ID.has(confl, id) && constraint_ID[confl]));
    printf("Conflict %s: ", primary_type ? "clause" : "term");
    printClause(confl);
    printTrail();
    vec<Lit> lits;
    if (primary_type) {
        for (int i = 0; i < ca[confl].size(); i++) lits.push(ca[confl][i]);
        traceReduction(lits, primary_type);
    }
    #endif

    vec<int> decision_level_counts(decisionLevel() + 1);
    int rightmost_depth = -1;

    Clause& c = ca[confl];

    for (int i = 0; i < c.size(); i++) {
        Var v = var(c[i]);
        assert(v < nVars());
        if (variable_type[v] == primary_type && rightmost_depth < variable_depth[v]) {
            rightmost_depth = variable_depth[v];
        }
    }
    if (rightmost_depth > -1) {
        for (int i = 0; i < c.size(); i++) {
            Var v = var(c[i]);
            assert(v >= 0);
            if (variable_depth[v] <= rightmost_depth) {
                assert(level(v) >= 0);
                decision_level_counts[level(v)]++;
                seen_at[v] = variables_at[variable_depth[v]].size();
                variables_at[variable_depth[v]].push(v);
                varBumpActivity(v);
            }
        }
    }

    int max_dl = decisionLevel();
    while (max_dl && !decision_level_counts[max_dl]) max_dl--;
    int index = trail.size() - 1;
    int dl_start = max_dl ? trail_lim[max_dl - 1] : 0;
    Var leftmost_blocked_var = var_Undef;
    Var asserting_variable = (decision_level_counts[max_dl] > 1) ? var_Undef : getAssertingVar(rightmost_depth, max_dl);

    // Keep going while the clause/term is not asserting.
    while (rightmost_depth > -1 && (max_dl == 0 || decision_level_counts[max_dl] > 1 || (mode == 0 && variable_type[asserting_variable] == other_type))) {
        assert(leftmost_blocked_var == var_Undef || level(leftmost_blocked_var) == max_dl || (mode == 0 && variable_type[asserting_variable] == other_type));
#ifndef NDEBUG
        printf("Maximum DL: %d\n", max_dl);
        printf("Current %s: ", primary_type ? "clause" : "term");
        printVariablesAt(rightmost_depth);
        if (leftmost_blocked_var != var_Undef) {
            printf("Leftmost blocked: %d\n", variable_names[leftmost_blocked_var]);
        }
        if (decision_level_counts[max_dl] == 1) {
            printf("(Potentially) asserting: %d\n", variable_names[asserting_variable]);
        }
#endif
        assert(mode == 1 || decision_level_counts[max_dl] > 1 || asserting_variable == getAssertingVar(rightmost_depth, max_dl));
        // While at max_dl, take next variable.
        // If leftmost blocking, update.
        // Afterwards:
        // - Resolve out blocking primaries 

        while(seen_at[var(trail[index--])] < 0);
        assert(index + 1 >= 0);
        assert(index + 1 < trail.size());
        Var pivot = var(trail[index + 1]);

        if (index + 1 >= dl_start) {
            if (variable_type[pivot] == other_type && (reason(pivot) == CRef_Undef || reasonType(pivot) != ct)) {
                leftmost_blocked_var = (leftmost_blocked_var == var_Undef || pivot < leftmost_blocked_var) ? pivot : leftmost_blocked_var;
                continue;
            } else if (variable_type[pivot] == primary_type && reason(pivot) == CRef_Undef && pivot < leftmost_blocked_var)
                continue;
        } else {
            assert(max_dl == 0 || leftmost_blocked_var != var_Undef); // || (mode == 0 && variable_type[asserting_variable] == other_type)); // Otherwise should be asserting.
            // if (mode == 0) {
            //     if (variable_type[pivot] == other_type && level(pivot) == max_dl && reason(pivot) == CRef_Undef) {
            //         asserting_variable = pivot;
            //     }
            // } else {
                if (variable_type[pivot] == other_type || (max_dl > 0 && pivot < leftmost_blocked_var))
                    continue;
            //if (variable_type[pivot] == other_type || ((leftmost_blocked_var == var_Undef || pivot < leftmost_blocked_var) && (asserting_variable == var_Undef || pivot < asserting_variable))) continue;
        }

#ifndef NDEBUG
        printf("Pivot: %d\n", variable_names[pivot]);
#endif

        confl = reason(pivot);
        if (confl != CRef_Undef && reasonType(pivot) != ct) {
            ct = reasonType(pivot);
            clearSeenAt(rightmost_depth);
            r = pivot;
            vardata[r].reason = CRef_Undef;
            goto analyzeStart;
        }
        if (confl == CRef_Undef) {
            assert(use_dependency_learning);
            assert(leftmost_blocked_var != var_Undef || asserting_variable != var_Undef);
            Var var_dependency = (leftmost_blocked_var != var_Undef && leftmost_blocked_var < pivot) ? leftmost_blocked_var : asserting_variable;
            learn_dependency = true;
            out_learnt.clear();
            out_learnt.push(mkLit(pivot, false));
            out_learnt.push(mkLit(var_dependency, false));
            out_btlevel = level(pivot) - 1;
            assert(out_btlevel >= 0);
            clearSeenAt(rightmost_depth);
            return;
        }
        if (trace) {
            uint64_t id;
            assert(constraint_ID.has(confl, id));
            id = constraint_ID[confl];
            premise_ids.push(id);
        }
        assert(constraint_type[confl] == ct);
#ifndef NDEBUG
        assert(!trace || (constraint_ID.has(confl, id) && constraint_ID[confl]));
        printf("Reason %s: ", primary_type ? "clause" : "term");
        printClause(confl);
        //if (primary_type) traceResolvent(quantifier_blocks[rightmost_depth].last(), pivot, r, primary_type);
#endif
        Var w = variables_at[variable_depth[pivot]].last();
        variables_at[variable_depth[pivot]][seen_at[pivot]] = w;
        variables_at[variable_depth[pivot]].pop();
        seen_at[w] = seen_at[pivot];
        seen_at[pivot] = -1;
        decision_level_counts[level(pivot)]--;

        Clause& c = ca[confl];
        assert(var(c[0]) == pivot);

        if (c.learnt())
            claBumpActivity(c);

        if (mode == 0 && pivot == asserting_variable) {
            asserting_variable = var_Undef;
        }

        // Account for new primary variables. Check whether one of them is right of the old rightmost primary variable.
        for (int j = 1; j < c.size(); j++) {
            Var v = var(c[j]);
            if (variable_type[v] == primary_type && seen_at[v] == -1) {
                seen_at[v] = variables_at[variable_depth[v]].size();
                variables_at[variable_depth[v]].push(v);
                varBumpActivity(v);
                decision_level_counts[level(v)]++;
                if (rightmost_depth < variable_depth[v]) { // TODO: Branchless alternative?
                    rightmost_depth = variable_depth[v];
                }
            }
        }
        // If no new rightmost primary was found, search from the old rightmost primary, reducing along the way.
        while (rightmost_depth > -1 && (quantifier_blocks_type[rightmost_depth] == other_type || !variables_at[rightmost_depth].size())) {
            for (int i = 0; i < variables_at[rightmost_depth].size(); i++) {
                Var v = variables_at[rightmost_depth][i];
                seen_at[v] = -1;
                decision_level_counts[level(v)]--;
            }
            variables_at[rightmost_depth].clear();
            rightmost_depth--;
        }
        // Add blocked universal variables from reason clause.
        if (rightmost_depth > -1) {
            if (rightmost_depth < variable_depth[leftmost_blocked_var]) {
                leftmost_blocked_var = var_Undef;
            }
            for (int j = 1; j < c.size(); j++) {
                Var v = var(c[j]);
                if (seen_at[v] == -1 && variable_type[v] == other_type && variable_depth[v] < rightmost_depth) {
                    seen_at[v] = variables_at[variable_depth[v]].size();
                    variables_at[variable_depth[v]].push(v);
                    varBumpActivity(v);
                    decision_level_counts[level(v)]++;
                }
            }
            // Check if the maximum decision level present in the current clause/term has changed.
            if (!decision_level_counts[max_dl]) {
                while (max_dl && !decision_level_counts[max_dl]) max_dl--;
                index = trail_lim[max_dl] - 1;
                dl_start = max_dl ? trail_lim[max_dl - 1] : 0;
                leftmost_blocked_var = var_Undef;
            }
            if (mode == 0 && (asserting_variable == var_Undef || rightmost_depth < variable_depth[asserting_variable])) {
                asserting_variable = (decision_level_counts[max_dl] > 1)? var_Undef: getAssertingVar(rightmost_depth, max_dl);
            }
        }
    }
    // The clause represented in "seen" is empty or asserting, translate back to vector.
    out_learnt.clear();
    if (rightmost_depth > -1) {
        int max_dl_var_index = 0;
        for (int d = 0; d <= rightmost_depth; d++) {
            for (int i = 0; i < variables_at[d].size(); i++) {
                Var v = variables_at[d][i];
                out_learnt.push(v == r? ~mkLit(v, primary_type ^ toInt(value(v))) : mkLit(v, primary_type ^ toInt(value(v))));
                max_dl_var_index = (level(v) > level(var(out_learnt[max_dl_var_index]))) ? out_learnt.size() - 1 : max_dl_var_index;
                seen_at[v] = -1;
                seen[v] = 1;
            }
            variables_at[d].clear();
        }
        // Move max dl. variable to index 0.
        Lit tmp = out_learnt[0];
        out_learnt[0] = out_learnt[max_dl_var_index];
        out_learnt[max_dl_var_index] = tmp;
    }
#ifndef NDEBUG
    printf("Learned %s before:    ", primary_type ? "clause" : "term");
    printClause(out_learnt);
#endif

    // Clause minimization. TODO: Can mode 1 be better than mode 2?
    out_learnt.copyTo(analyze_toclear);
    int i, j;
    if (ccmin_mode == 2) {
             for (i = j = 1; i < out_learnt.size(); i++)
                 if (reason(var(out_learnt[i])) == CRef_Undef || reasonType(var(out_learnt[i])) != ct || !litRedundant(out_learnt[i], ct))
                     out_learnt[j++] = out_learnt[i];
    } else if (ccmin_mode == 1) {
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);
            if (reason(x) == CRef_Undef || reasonType(x) != ct)
                out_learnt[j++] = out_learnt[i];
            else {
                Clause& c = ca[reason(x)];
                #ifndef NDEBUG
                printf("Checking for local redundancy of %d\n", variable_names[x]);
                printf("Reason: ");
                printClause(reason(x));
                #endif
                assert(var(c[0]) == x && reasonType(x) == ct);
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && (level(var(c[k])) > 0 || reasonType(var(c[k])) != ct || ca[reason(var(c[k]))].size() > 1)) {
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    } else if (ccmin_mode == 3) {
        i = out_learnt.size();
        j = minimize(out_learnt, ct);
    } else {
        i = j = out_learnt.size();
    }

    if (out_learnt.size()) {
        Var rightmost_primary = var_Undef;
        for (int k = 0; k < j; k++) {
            Var v = var(out_learnt[k]);
            rightmost_primary = (rightmost_primary < v && variable_type[v] == primary_type) ? v : rightmost_primary;
        }
        if (rightmost_primary == var_Undef) {
            j = 1;
        } else {
            int k, h;
            for (h = k = 1; k < j; k++) {
                if (variable_type[var(out_learnt[k])] == primary_type || var(out_learnt[k]) < rightmost_primary)
                    out_learnt[h++] = out_learnt[k];
            }
            j = h;
        }
    } else {
        i = j = 0;
    }

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    #ifndef NDEBUG
    if (j < i) {
        printf("Minimized learned %s: ", primary_type ? "clause" : "term");
        printClause(out_learnt);
    }
    #endif

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

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

    if (trace) {
        auto id = running_id;
        traceConstraint(id, ct, out_learnt, premise_ids);
    }

    // for (int i = 0; i < out_learnt.size(); i++) {
    //     varBumpActivity(var(out_learnt[i]), var_inc * ((double)learnts_literals[ct]/nLearnts(ct) - out_learnt.size()));
    // }
}

int Solver::minimize(Lit lit, int asserting_level, bool constraint_type, int depth) {
    auto v = var(lit);
    if (depth > 1000)
        return 0; // 0 is "poison".
    if (depth && seen[v])
        return INT_MAX;
    if (removable_if[v] > -1)
        return removable_if[v];
    if (level(v) == asserting_level)
        return 0;
    if (variable_type[v] == constraint_type)
        return variable_depth[v];
    CRef cr = reason(v);
    if (cr == CRef_Undef || reasonType(v) != constraint_type)
        return 0;
    Clause& c = ca[cr];
    int res = INT_MAX;
    assert(v == var(c[0]));
    for (int i = 1; i < c.size(); i++) {
        Lit other_lit = c[i];
        auto res_ = minimize(other_lit, asserting_level, constraint_type, depth + 1);
        if (res_ < res)
            res = res_;
        if (!res)
            break;
    }
    minimize_seen.push(v);
    return removable_if[v] = res;
}

int Solver::minimize(vec<Lit>& lits, bool constraint_type) {
    if (!lits.size())
        return 0;
    // We assume that the first literal is asserting.
    auto alevel = level(var(lits[0]));
    int innermost_depth = variable_depth[var(lits[0])];
    MinimizeLT minimize_lt(*this, alevel, constraint_type);
    sort(&lits[1], lits.size() - 1, minimize_lt);
    int i, j;
    for (i = j = 1; i < lits.size(); i++) {
        auto v = var(lits[i]);
        if (minimize(lits[i], alevel, constraint_type) <= innermost_depth) {
            lits[j++] = lits[i];
            if (variable_type[v] != constraint_type && innermost_depth < variable_depth[v])
                innermost_depth = variable_depth[v];
        }
    }
    for (int i = 0; i < minimize_seen.size(); i++)
        removable_if[minimize_seen[i]] = -1;
    minimize_seen.clear ();
    return j;
}

void Solver::analyzeLDQ(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, bool& learn_dependency, bool& ct) {
    learn_dependency = false;
    bool primary_type = (ct == ConstraintTypes::Clauses);
    bool other_type = !primary_type;
    Var asserting_variable, second_watcher_variable;
    int iterations = 0;

    vec<int> decision_level_counts(decisionLevel() + 1);
    int rightmost_depth = -1;

    #ifndef NDEBUG
    printf("Conflict: ");
    printClause(confl);
    #endif

    Clause& c = ca[confl];

    for (int i = 0; i < c.size(); i++) {
        Var v = var(c[i]);
        assert(v < nVars());
        if (variable_type[v] == primary_type) {
            seen[v] = 1;
            rightmost_depth = (rightmost_depth < variable_depth[v]) ? variable_depth[v] : rightmost_depth;
            decision_level_counts[level(v)]++;
        }
    }
    if (rightmost_depth > -1) {
        for (int i = 0; i < c.size(); i++) {
            Var v = var(c[i]);
            assert(v >= 0);
            if (variable_depth[v] <= rightmost_depth) {
                varBumpActivity(v);
                assert(value(v) == l_Undef || level(v) >= 0);
                seen_at[toInt(c[i])] = variables_at[variable_depth[v]].size();
                variables_at[variable_depth[v]].push(toInt(c[i]));
            }
        }
    }

    int max_dl = decisionLevel();
    while (max_dl && !decision_level_counts[max_dl]) max_dl--;
    int index = trail.size();

    #ifndef NDEBUG
    printTrail();
    #endif
    while (rightmost_depth > -1 && (max_dl == 0 || decision_level_counts[max_dl] > 1 || !isAsserting(rightmost_depth, asserting_variable = getAssertingVarLDQ(rightmost_depth, max_dl), second_watcher_variable))) {
        iterations++;
        assert(iterations < 2*trail.size());
        Var pivot = nextPivot(index);
        if (pivot == var_Undef) {
            // All remaining primary variables are assigned by decision.
            // In particular, that is the case for the rightmost primary.
            assert(use_dependency_learning);
            Var rightmost_primary = var(toLit(variables_at[rightmost_depth].last()));
            // Find variable left of pivot that is unassigned or was assigned after the rightmost primary.
            Var var_dependency = getBlockedVariable(rightmost_primary);
            learn_dependency = true;
            out_learnt.clear();
            out_learnt.push(mkLit(rightmost_primary, false));
            out_learnt.push(mkLit(var_dependency, false));
            out_btlevel = level(rightmost_primary) - 1;
            assert(out_btlevel >= 0);
            for (int d = 0; d <= rightmost_depth; d++) {
                for (int i = 0; i < variables_at[d].size(); i++) {
                    auto l = variables_at[d][i];
                    seen[var(toLit(l))] = 0;
                }
            }
            clearSeenAt(rightmost_depth);
            return;
        }
        #ifndef NDEBUG
        printf("Pivot: %d\n", variable_names[pivot]);
        #endif
        assert(reason(pivot) != CRef_Undef);
        Clause& c = ca[reason(pivot)];
        if (c.learnt())
            claBumpActivity(c);
        #ifndef NDEBUG
        printf("Reason: ");
        printClause(reason(pivot));
        #endif

        // Remove pivot variable from current clause/term.
        int pivot_int = toInt(mkLit(pivot, primary_type ^ toInt(value(pivot))));
        // Swap with last variable at this depth to keep seen_at intact.
        int w = variables_at[variable_depth[pivot]].last();
        variables_at[variable_depth[pivot]][seen_at[pivot_int]] = w;
        variables_at[variable_depth[pivot]].pop();
        seen_at[w] = seen_at[pivot_int];
        seen_at[pivot_int] = -1;
        decision_level_counts[level(pivot)]--;
        seen[pivot] = 0;

        for (int j = 1; j < c.size(); j++) {
            Lit q = c[j];
            Var v = var(c[j]);
            if (variable_type[v] == primary_type && seen_at[toInt(q)] == -1) {
                seen[v] = 1;
                seen_at[toInt(q)] = variables_at[variable_depth[v]].size();
                variables_at[variable_depth[v]].push(toInt(q));
                varBumpActivity(v);
                decision_level_counts[level(v)]++;
                if (rightmost_depth < variable_depth[v]) {
                    rightmost_depth = variable_depth[v];
                }
            }
        }
        if (level(pivot) == max_dl) {
            while (max_dl && !decision_level_counts[max_dl]) max_dl--;
        }

        // If no new rightmost primary was found, search from the old rightmost primary, reducing along the way.
        while (rightmost_depth > -1 && (quantifier_blocks_type[rightmost_depth] == other_type || !variables_at[rightmost_depth].size())) {
            for (int i = 0; i < variables_at[rightmost_depth].size(); i++) {
                seen_at[variables_at[rightmost_depth][i]] = -1;
            }
            variables_at[rightmost_depth].clear();
            rightmost_depth--;
        }
        // Add blocked universal variables from reason clause.
        if (rightmost_depth > -1) {
            for (int j = 1; j < c.size(); j++) {
                int lit_int = toInt(c[j]);
                Var v = var(c[j]);
                if (seen_at[lit_int] == -1 && variable_type[v] == other_type && variable_depth[v] < rightmost_depth) {
                    seen_at[lit_int] = variables_at[variable_depth[v]].size();
                    variables_at[variable_depth[v]].push(lit_int);
                    varBumpActivity(v);
                }
            }
        }
    }

    int asserting_index = -1;
    int second_watcher_index = -1;

    for (int d = 0; d <= rightmost_depth; d++) {
        for (int i = 0; i < variables_at[d].size(); i++) {
            Lit p = toLit(variables_at[d][i]);
            if (var(p) == asserting_variable)
                asserting_index = out_learnt.size();
            else if (var(p) == second_watcher_variable)
                second_watcher_index = out_learnt.size();
            out_learnt.push(p);
        }
    }
    clearSeenAt(rightmost_depth);

    if (out_learnt.size() > 1) {
        Lit p = out_learnt[asserting_index];
        out_learnt[asserting_index] = out_learnt[0];
        out_learnt[0] = p;
        second_watcher_index = (second_watcher_index == 0) ? asserting_index : second_watcher_index;
        p = out_learnt[second_watcher_index];
        out_learnt[second_watcher_index] = out_learnt[1];
        out_learnt[1] = p;
        out_btlevel = level(var(p));
    } else {
        out_btlevel = 0;
    }

    #ifndef NDEBUG
    printf("Learnt %s: ", primary_type ? "clause" : "term");
    printClause(out_learnt);
    #endif
 
    for (int i = 0; i < out_learnt.size(); i++)
        seen[var(out_learnt[i])] = 0;
}

// Check if 'p' can be removed from a conflict clause.
bool Solver::litRedundant(Lit p, bool ct)
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
            if (seen[var(l)] == seen_source || seen[var(l)] == seen_removable || (level(var(l)) == 0 && reasonType(var(l)) == ct && ca[reason(var(l))].size() == 1)) {
                continue; }
            
            // Check variable can not be removed for some local reason:
            if (reason(var(l)) == CRef_Undef || reasonType(var(l)) != ct || seen[var(l)] == seen_failed) {
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
            assert(reasonType(var(p)) == ct);
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
            assert(reasonType(var(p)) == ct);

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


void Solver::uncheckedEnqueue(Lit p, CRef from, bool constraint_type)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel(), constraint_type);
    trail.push_(p);
    if (!use_dependency_learning) quantifier_blocks_unassigned[variable_depth[var(p)]]--;
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
    Lit     q         = lit_Undef;
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
                if (value(first) == l_vanishing || (mode == 0 && variable_type[var(first)] == (ct_ == ConstraintTypes::Terms))) {
                    // Clause falsified.
                    q = first;
                    ct = ct_;
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                } else {
                    uncheckedEnqueue(ct_ == Clauses ? first : ~first, cr, ct_);
                }

            NextClause:;
            }
            ws.shrink(i - j);
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;

    if (mode == 0 && q != lit_Undef && value(q) == l_Undef) {
        uncheckedEnqueue(ct == Clauses ? ~q : q);
    }

    return confl;
}

CRef Solver::propagateLDQ(bool& ct)
{
    CRef    confl     = CRef_Undef;
    Lit     q         = lit_Undef;
    int     num_props = 0;

    while (qhead < trail.size()){
        num_props++;
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        
        for (auto ct_ : { Clauses, Terms } ) {
            lbool l_disabling = (ct_ == Clauses) ? l_True : l_False;
            lbool l_vanishing = (ct_ == Clauses) ? l_False : l_True;
            bool primary = (ct_ == Clauses);
            bool secondary = !primary;

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
                i++;
                // Skip spurious entries.
                if (c[1] != false_lit) {
                    continue;    
                }

                #ifndef NDEBUG
                printTrail();
                printf("Propagating %s: ", primary ? "clause": "term");
                printClause(cr);
                #endif

                // If 0th watch is true, then clause is already satisfied.
                Lit     first = c[0];
                Watcher w     = Watcher(cr, first);
                if (first != blocker && value(first) == l_disabling) {
                    *j++ = w;
                    continue; 
                }

                // If a literal satisfies the clause, do not touch the watchers.
                int k;
                for (k = 2; k < c.size(); k++) {
                    if (value(c[k]) == l_disabling) {
                        break;
                    }
                }
                if (k < c.size()) {
                    *j++ = w;
                    continue;
                }

                // Every remaining literal is unassigned or falsified.
                if (variable_type[var(first)] == primary) {
                    // Look for new primary watch or secondary that is blocked by var(first).
                    for (int k = 2; k < c.size(); k++)
                        if (value(c[k]) != l_vanishing && (variable_type[var(c[k])] == primary || var(c[k]) < var(first))) {
                            c[1] = c[k]; c[k] = false_lit;
                            (*watches[ct_])[(ct_ == Clauses) ? ~c[1] : c[1]].push(w);
                            goto NextClause; }
                } else {
                    // First literal is a secondary literal.
                    // Find a new primary to watch.
                    for (k = 2; k < c.size(); k++)
                        if (value(c[k]) != l_vanishing && variable_type[var(c[k])] == primary)
                            break;
                    if (k < c.size()) {
                        // New primary found. Try to find a new primary or secondary that is blocked by var(c[0]);
                        c[0] = c[k];
                        c[k] = first;
                        (*watches[ct_])[(ct_ == Clauses) ? ~c[0] : c[0]].push(w);
                        for (int h = 2; h < c.size(); h++)
                            if (value(c[h]) != l_vanishing && (variable_type[var(c[h])] == primary || var(c[h]) < var(c[0]))) {
                                c[1] = c[h]; c[h] = false_lit;
                                // Check if new watcher happens to be the original first literal. This clause is already on its watched list.
                                if (first != c[h])
                                    (*watches[ct_])[(ct_ == Clauses) ? ~c[1] : c[1]].push(w);
                                goto NextClause;
                            }
                        // No new second watcher found. Clause/term is unit and c[1] (primary) remains a watcher.
                        first = c[0];
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if (value(first) == l_vanishing || variable_type[var(first)] == secondary) {
                    // Clause falsified.
                    q = first;
                    ct = ct_;
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                } else {
                    uncheckedEnqueue(ct_ == Clauses ? first : ~first, cr, ct_);
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
    CMap<int>& LBDs;
    reduceDB_lt(ClauseAllocator& ca_, CMap<int>& LBDs_) : ca(ca_), LBDs(LBDs_) {}
    bool operator () (CRef x, CRef y) { 
        return LBDs[x] > LBDs[y] || (LBDs[x] == LBDs[y] && (ca[x].activity() < ca[y].activity())); }
};
void Solver::reduceDB()
{
    int     i, j;
    sort(learnts, reduceDB_lt(ca, constraint_LBD));
    int learnt_counts[2] = {0, 0};
    for (int i = 0; i < learnts.size(); i++)
        learnt_counts[constraint_type[learnts[i]]]++;
    // Don't delete binary or locked constraints. From the rest, delete constraints from the first half:
    int learnts_removed[2] = {0, 0};
    for (i = j = 0; i < learnts.size(); i++) {
        Clause& c = ca[learnts[i]];
        auto c_type = constraint_type[learnts[i]];
        if (constraint_LBD[learnts[i]] > 2 && !locked(c) && (learnts_removed[c_type] < (learnt_counts[c_type] / 2))) {
            removeClause(learnts[i]);
            learnts_removed[c_type]++;
        } else
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
    order_heaps[0]->build(vs);
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
    simpDB_props   = clauses_literals + learnts_literals[ConstraintTypes::Clauses];   // (shouldn't depend on stats really, but it will do for now)

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
        CRef confl = (mode == 2) ? propagateLDQ(ct) : propagate(ct);
        if (confl != CRef_Undef){
            // CONFLICT
            conflict: // goto label
        
            conflicts++; conflictC++;

            learnt_clause.clear();
            if (mode == 2) {
                analyzeLDQ(confl, learnt_clause, backtrack_level, learn_dependency, ct);
            } else {
                analyze(confl, learnt_clause, backtrack_level, learn_dependency, ct);
            }
            if (learnt_clause.size() == 0) return (ct == Clauses) ? l_False : l_True;
            if (learn_dependency) {
                nr_dependencies++;
                assert(learnt_clause.size() == 2);
                Var x = var(learnt_clause[0]);
                Var y = var(learnt_clause[1]);
                assert(!hasDependency(x, y));
                #ifndef NDEBUG
                printf("Learned dependency of %d on %d.\n", variable_names[x], variable_names[y]);
                #endif
                dependencies[x].push(y);
                dependencies[x].last() = dependencies[x][0];
                dependencies[x][0] = y;
                dependency_watched_variables[y].push(x);
                cancelUntil(backtrack_level);
                if (order_heaps[0]->inHeap(x)) {
                    order_heaps[0]->remove(x);
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
                int lbd = computeLBD(learnt_clause);
                cancelUntil(backtrack_level);
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                constraint_type.insert(cr, ct);
                constraint_LBD.insert(cr, lbd);
                if (trace) {
                    auto id = running_id++;
                    constraint_ID.insert(cr, id);
                }
                if (learnt_clause.size() > 1) {
                    attachClause(cr);
                    claBumpActivity(ca[cr]);
                }
                assert(mode == 1 || variable_type[var(learnt_clause[0])] == (ct == ConstraintTypes::Clauses));
                uncheckedEnqueue((ct == Clauses) ? learnt_clause[0] : ~learnt_clause[0], cr, ct);


                varDecayActivity();
                claDecayActivity();

                if (--learntsize_adjust_cnt == 0){
                    learntsize_adjust_confl *= learntsize_adjust_inc;
                    learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                    max_learnts             *= learntsize_inc;

                    if (verbosity >= 1)
                        printf("| %9d | %12d | %8d %8d %6.0f %8d %6.0f | %6.3f %% |\n", 
                            (int)conflicts,
                            (int)nr_dependencies,
                            (int)max_learnts,
                            nLearnts(ConstraintTypes::Clauses), (double)learnts_literals[ConstraintTypes::Clauses]/ nLearnts(ConstraintTypes::Clauses),
                            nLearnts(ConstraintTypes::Terms),   (double)learnts_literals[ConstraintTypes::Terms]  / nLearnts(ConstraintTypes::Terms),
                            random_var_freq * 100);
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
        printf("==============================[ Search Statistics ]===============================\n");
        printf("| Conflicts | Dependencies |           LEARNT                         | rnd_freq |\n");
        printf("|           |              |   Limit   Clauses Lit/Cl    Terms  Lit/T |          |\n");
        printf("==================================================================================\n");
    }

    allocInitialTerm();
    initOrderHeaps();
    //addInitialTerms();

    status = input_status;

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
        if (use_dependency_learning && (curr_restarts + 1) % 20 == 0) resetDependencies();
        random_var_freq *= 0.995;
    }

    if (verbosity >= 1)
        printf("==================================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    saveOutermostAssignment();
    cancelUntil(0);
    // TODO: Why can't we do the following in the destructor?
    if (trace) {
        trace_file.flush();
    }
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
    printf("restarts              : %" PRIu64 "\n", starts);
    printf("conflicts             : %-12" PRIu64 "   (%.0f /sec)\n", conflicts   , conflicts   /cpu_time);
    printf("dependencies          : %-12" PRIu64 "   (%.2f /conflict) \n", nr_dependencies, (float)nr_dependencies/(float)conflicts);
    printf("decisions             : %-12" PRIu64 "   (%4.2f %% random) (%.0f /sec)\n", decisions, (float)rnd_decisions*100 / (float)decisions, decisions   /cpu_time);
    printf("propagations          : %-12" PRIu64 "   (%.0f /sec)\n", propagations, propagations/cpu_time);
    printf("conflict literals     : %-12" PRIu64 "   (%4.2f %% deleted)\n", tot_literals, (max_literals - tot_literals)*100 / (double)max_literals);
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
    CMap<int>  constraint_LBD_;
    CMap<uint64_t> constraint_ID_;
    uint64_t id;
    //std::unordered_map<unsigned int, bool> constraint_type_;

    // All learnt:
    //
    int i, j;
    for (i = j = 0; i < learnts.size(); i++)
        if (!isRemoved(learnts[i])){
            auto ct = constraint_type[learnts[i]];
            auto lbd = constraint_LBD[learnts[i]];
            if (trace)
                id = constraint_ID[learnts[i]];
            ca.reloc(learnts[i], to);
            constraint_type_.insert(learnts[i], ct);
            constraint_LBD_.insert(learnts[i], lbd);
            if (trace)
                constraint_ID_.insert(learnts[i], id);
            learnts[j++] = learnts[i];
        }
    learnts.shrink(i - j);

    // All original:
    //
    for (i = j = 0; i < clauses.size(); i++)
        if (!isRemoved(clauses[i])){
            if (trace)
                id = constraint_ID[clauses[i]];
            ca.reloc(clauses[i], to);
            constraint_type_.insert(clauses[i], Clauses);
            if (trace)
                constraint_ID_.insert(clauses[i], id);
            clauses[j++] = clauses[i];
        }
    clauses.shrink(i - j);

    // Initial term:
    Clause& initial_term = ca[initial_term_ref];
    initial_term.setSize(nVars());
    ca.reloc(initial_term_ref, to);
    constraint_type_.insert(initial_term_ref, ConstraintTypes::Terms);
    if (trace)
        constraint_ID_.insert(initial_term_ref, 0);

    // All terms:
    //
    for (i = j = 0; i < terms.size(); i++)
        if (!isRemoved(terms[i])){
            if (trace)
                id = constraint_ID[terms[i]];
            ca.reloc(terms[i], to);
            constraint_type_.insert(terms[i], Terms);
            if (trace)
                constraint_ID_.insert(terms[i], id);
            terms[j++] = terms[i];
        }
    terms.shrink(i - j);

    constraint_type_.moveTo(constraint_type);
    constraint_LBD_.moveTo(constraint_LBD);
    constraint_ID_.moveTo(constraint_ID);
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
    if (trace) {
        auto id = running_id++;
        constraint_ID[initial_term_ref] = id;
        traceInitialTerm();
    }
}

void Solver::printClause(CRef cr) const {
    const Clause& c = ca[cr];
    for (int i = 0; i < c.size(); i++) {
        Lit p = c[i];
        Var v = variable_names[var(p)];
        printf("%c%d", variable_type[var(p)] ? 'e' : 'a', sign(p) ? -v : v);
        if (value(var(p)) != l_Undef)
            printf("@%d", level(var(p)));
        printf(" ");
    }
    printf("\n");
}

void Solver::printClause(const vec<Lit>& literals) const {
    for (int i = 0; i < literals.size(); i++) {
        Lit p = literals[i];
        Var v = variable_names[var(p)];
        printf("%c%d", variable_type[var(p)] ? 'e' : 'a', sign(p) ? -v : v);
        if (value(var(p)) != l_Undef)
            printf("@%d", level(var(p)));
        printf(" ");
    }
    printf("\n");
}

void Solver::printTrail() const {
    printf("Trail: ");
    for (int i = 0; i < trail.size(); i++) {
        Lit p = trail[i];
        Var v = variable_names[var(p)];
        printf("%c%d@%d ", variable_type[var(p)] ? 'E' : 'A', sign(p) ? -v : v, level(var(p)));
        if (reason(var(p)) != CRef_Undef) {
            printf("(%s) ", reasonType(var(p)) == Clauses ? "clause" : "term");
        }
    }
    printf("\n");
}

void Solver::printSeen(Var rightmost) const {
    for (int v = 0; v <= rightmost; v++) {
        if (seen[v]) {
            printf("%c%d@%d ", variable_type[v] ? 'e' : 'a', variable_names[v], level(v));
        }
    }
    printf("\n");
}

void Solver::printVariablesAt(int rightmost_depth) const {
    for (int d = 0; d <= rightmost_depth; d++) {
        for (int i = 0; i < variables_at[d].size(); i++) {
            Var v = variables_at[d][i];
            printf("%c%d@%d ", variable_type[v] ? 'e' : 'a', variable_names[v], level(v));
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
    constraint_type.insert(initial_term_ref, Terms);
    if (trace)
        constraint_ID.insert(initial_term_ref, 0);
}

lbool Solver::addTerm(const vec<Lit>& term) {
    vec<Lit> term_copy;
    term.copyTo(term_copy);

    sort(term_copy);

    // Check for contradictions.
    for (int i = 1; i < term_copy.size(); i++) {
        if (term_copy[i] == ~term_copy[i-1]) {
            return l_Undef;
        }
    }

    // Remove duplicate literals.
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < term_copy.size(); i++)
        if (term_copy[i] != p)
            term_copy[j++] = p = term_copy[i];
    term_copy.shrink(i - j);

    reduce(term_copy, false);

    CRef cr = ca.alloc(term_copy, false);
#ifndef NDEBUG
    printf("Adding term: ");
    printClause(term_copy);
#endif
    terms.push(cr);
    //constraint_type[cr] = Terms;
    constraint_type.insert(cr, Terms);
    if (trace)
        constraint_ID.insert(cr, running_id++);
    if (term_copy.size() == 0) {
        return input_status = l_True;
    }
    if (term_copy.size() == 1){
        Lit p = term_copy[0];
        if (variable_type[var(p)] || value(p) == l_True) {
            return input_status = l_True;
        } else {
            uncheckedEnqueue(~p, cr, ConstraintTypes::Terms);
            return l_Undef;
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
    return addTerm(term);
}

void Solver::initOrderHeaps() { 
    int nr_heaps = use_dependency_learning ? 1 : quantifier_blocks.size();
    order_heaps = new Heap<Var,VarOrderLt>*[nr_heaps];
    for (int i = 0; i < nr_heaps; i++) {
        order_heaps[i] = new Heap<Var,VarOrderLt>(VarOrderLt(activity)); 
    }
    for (Var v = 0; v < nVars(); v++) {
        insertVarOrder(v);
    }
}

int Solver::getDecisionBlock() {
    int i;
    for (i = 0; i < quantifier_blocks.size() && quantifier_blocks_unassigned[i] == 0; i++);
    // ONLY QCIR interface assert(i < quantifier_blocks.size()-2);
    return i;
}

void Solver::traceVector(const vec<Lit>& lits, bool newline) {
    for (int i = 0; i < lits.size(); i++) {
        Lit p = lits[i];
        trace_file << (sign(p) ? -variable_names[var(p)] : variable_names[var(p)]) << " ";
    }
    trace_file << "0";
    if (newline)
        trace_file << "\n";
    else
        trace_file << " ";
}

void Solver::traceResolvent(Var rightmost_primary, Var pivot, Var r, bool primary_type) {
    vec<Lit> current;
    for (int v = 0; v <= rightmost_primary; v++) {
        if (v != pivot && v != r && seen[v])
            current.push(mkLit(v, primary_type ^ toInt(value(v))));
    }
    if (r != var_Undef && seen[r]) {
        current.push(~mkLit(r, primary_type ^ toInt(value(r))));
    }
    Clause& c = ca[reason(pivot)];
    for (int i = 1; i < c.size(); i++) {
        current.push(c[i]);
    }
    sort(current, lt_lits);
    int i, j;
    for (i = 1, j = 0; i < current.size(); i++) {
        if (current[i] != current[j]) {
            current[++j] = current[i];
        }
    }
    current.shrink(i - j - 1);
    traceVector(current);
    traceReduction(current, primary_type);
}

void Solver::traceReduction(vec<Lit>& lits, bool primary_type) {
    sort(lits, lt_lits);
    while (lits.size() && variable_type[var(lits.last())] != primary_type) {
        trace_file << "u ";
        traceVector(lits);
        lits.pop();
        traceVector(lits);
    }
}

void Solver::traceConstraint(uint64_t id, bool constraint_type, const vec<Lit>& lits, const vec<uint64_t>& premise_ids) {
    trace_file << id << " " << int(constraint_type) << " ";
    traceVector(lits, false);
    for (int i = 0; i < premise_ids.size(); i++) {
        uint64_t premise_id = premise_ids[i];
        trace_file << premise_id << " ";
    }
    trace_file << "0 \n";
}

void Solver::traceInitialTerm() {
    uint64_t id = constraint_ID[initial_term_ref];
    trace_file << id << " " << int(ConstraintTypes::Terms) << " ";
    auto& initial_term = ca[initial_term_ref];
    for (int i = 0; i < initial_term.size(); i++) {
        Lit p = initial_term[i];
        trace_file << (sign(p) ? -variable_names[var(p)] : variable_names[var(p)]) << " ";
    }
    trace_file << "0 0\n";
}

void Solver::resetDependencies() {
    for (Var v = 0; v < nVars(); v++) {
        dependency_watched_variables[v].clear();
        dependencies[v].clear();
        insertVarOrder(v);
    }
    dqhead = 0;
    nr_dependencies = 0;
}

bool Solver::hasDependency(Var of, Var on) const {
    for (int i = 0; i < dependencies[of].size(); i++) {
        if (dependencies[of][i] == on) return true;
    }
    return false;
}

int Solver::computeLBD(vec<Lit>& lits) {
    IntSet<int> levels_present;
    for (int i = 0; i < lits.size(); i++) {
        Var v = var(lits[i]);
        if (value(v) != l_Undef)
            levels_present.insert(level(var(lits[i])));
    }
    return levels_present.size();
}

void Solver::reduce(vec<Lit>& lits, bool primary_type) {
    sort(lits);
    int i;
    for (i = lits.size(); i > 0; i--) {
        assert(i > 0);
        if (variable_type[var(lits[i-1])] == primary_type)
            break;
    }
    lits.shrink(lits.size() - i);
}


bool Solver::isAsserting(int rightmost_depth, Var asserting_variable, Var& second_watcher_variable) {
    // A clause is asserting if there is a unique existential of maximum dl (among existentials).
    // And each universal that it depends on is assigned at a lower dl.
    bool primary_type = quantifier_blocks_type[rightmost_depth];
    // There is a unique existential of maximum dl > 0.
    // Check for blocked secondaries.
    for (int d = 0; d < variable_depth[asserting_variable]; d++) {
        if (quantifier_blocks_type[d] == primary_type)
            continue;
        for (int i = 0; i < variables_at[d].size(); i++) {
            Var v = var(toLit(variables_at[d][i]));
            if (value(v) == l_Undef || level(v) >= level(asserting_variable))
                return false;
        }
    }
    // Finally, we need a second watcher.
    second_watcher_variable = var_Undef;
    int k = 0;
    for (int d = 0; d <= rightmost_depth; d++) {
        for (int i = 0; i < variables_at[d].size(); i++) {
            k++;
            Var v = var(toLit(variables_at[d][i]));
            if ((variable_type[v] == primary_type || (v < asserting_variable && value(v) != l_Undef)) && level(v) < level(asserting_variable) && (second_watcher_variable == var_Undef || level(second_watcher_variable) < level(v)))
                second_watcher_variable = v;
        }
    }
    return k == 1 || second_watcher_variable != var_Undef;
}

Var Solver::nextPivot(int& index) const {
    do {
        index--;
    } while (index >= 0 && (!seen[var(trail[index])] || reason(var(trail[index])) == CRef_Undef));
    if (index >= 0) {
        return var(trail[index]);
    } else {
        return var_Undef;
    }
}

void Solver::resolveWith(vec<Lit>& lits, const Clause& c, Var pivot) const {
    vec<Lit> resolvent;
    LSet lits_set;
    for (int i = 0; i < lits.size(); i++) {
        if (var(lits[i]) != pivot) {
            lits_set.insert(lits[i]);
            resolvent.push(lits[i]);
        }
    }
    for (int i = 0; i < c.size(); i++) {
        if (var(c[i]) != pivot && !lits_set.has(c[i])) {
            resolvent.push(c[i]);
        }
    }
    resolvent.moveTo(lits);
}

void Solver::getPartialCertificate(vec<Lit>& certificate) const {
    outermost_assignment.copyTo(certificate);
}

void Solver::saveOutermostAssignment() {
    for (int i = 0; i < quantifier_blocks[0].size(); i++) {
        Var internal_var = quantifier_blocks[0][i];
        Var original_var = variable_names[internal_var];
        bool last_sign = assigns[internal_var] == l_False;
        outermost_assignment.push(mkLit(original_var, last_sign));
    }
}