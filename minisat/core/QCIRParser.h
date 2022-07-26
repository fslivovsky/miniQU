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
    void initSolver(Minisat::Solver& solver);
    string getOriginalName(int alias) const;

  protected:
    QCIRParser();
    void readQuantifierBlock(const string& line);
    void readGate(const string& line);
    void readOutput(const string& line);
    void getVarAliases(Minisat::Solver& solver);
    std::vector<std::vector<int>> getClausalEncoding(bool get_terms);
    std::vector<std::vector<int>> getClausalEncoding(int gate_alias, bool get_terms);

    std::vector<GatePolarity> polarities;

    static const string EXISTS_STRING;
    static const string FORALL_STRING;
    static const string OUTPUT_STRING;
    static const string AND_STRING;
    static const string OR_STRING;

};

#endif