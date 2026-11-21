#ifndef QCIRParser_h
#define QCIRParser_h

#include <vector>
#include <string>

#include "QBFParser.h"
#include "Solver.h"

using std::vector;
using std::string;

class QCIRParser: virtual public QBFParser {
  public:
    QCIRParser(const string& filename);
    void initSolver(Minisat::Solver& solver, bool early_tseitin);
    string getOriginalName(int alias) const;

  protected:
    QCIRParser();
    void readQuantifierBlock(VariableType type, const string& variables_string);
    void readGate(const string& gate_id, const string& gate_type_string, const string& gate_inputs_string);
    void readOutput(const string& output_lit_str);
    void defineGate(const string& gate_id, GateType gate_type, const vector<string>& input_literals);
    void getVarAliases(Minisat::Solver& solver);
    std::vector<int> getGateDepths() const;
    std::vector<std::vector<int>> getClausalEncoding(int gate_alias, bool get_terms);

    std::vector<GatePolarity> polarities;
    std::unordered_map<int, int> gate_number; // Gates (by alias) numbered from 1 in the order of their definitions.

    static const string EXISTS_STRING;
    static const string FORALL_STRING;
    static const string OUTPUT_STRING;
    static const string AND_STRING;
    static const string OR_STRING;

};

#endif