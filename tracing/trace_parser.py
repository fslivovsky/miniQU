#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Jul 19 10:33:32 2018

@author: fs
"""

import mmap

COMMENT_TOKEN = 'c'
EXISTS_TOKEN = 'e'
FORALL_TOKEN = 'a'
EOL_TOKEN = '0'
END_CONSTRAINT_TOKEN = '0'

def is_negated(literal):
  return literal.startswith('-')

def var(literal):
  return literal[1:] if is_negated(literal) else literal

def neg(literal):
  return literal[1:] if literal.startswith('-') else '-' + literal

class TraceParser:
  
  def __init__(self, filename, extract_core=True):
    self.qtype = {}
    self.qdepth = {}
    self.constraints = {}
    self.constraint_type = {}
    self.constraint_in_core = {}
    self.premises = {}
    self.filename = filename
    self.attribute_names = None
    
    quantifier_lines = []
    constraints_processed = 0
    constraints_total = 1
    constraints_learned = 0
    constraints_learned_core = 0
    active_set = set()
    
    with open(filename) as trace:
      with mmap.mmap(trace.fileno(), 0, prot=mmap.PROT_READ) as mm:
        search_boundary = -1
        while True:
          file_position = mm.rfind(b'\n', 0, search_boundary) + 1
          search_boundary = file_position - 1
          mm.seek(file_position)
          line = mm.readline().decode()
          if line:
            if line.startswith(COMMENT_TOKEN):
              continue
            elif line.startswith(FORALL_TOKEN) or line.startswith(EXISTS_TOKEN):
              quantifier_lines.append(line)
            else:
              constraints_processed += 1
              if constraints_processed % 5000 == 0:
                print("{} of {} constraints processed ({:2.0f}%)".format(
                    constraints_processed,
                    constraints_total,
                    (constraints_processed/constraints_total) * 100
                    ))
              result = self.readTraceLine(line)
              constraint_id, constraint_type, constraint, premise_ids, attributes = result
              if not self.constraints: # Final constraint, mark as active.
                constraints_total = int(constraint_id)
                active_set.add(constraint_id)
                self.final_constraint_id = constraint_id
                self.proof_type = constraint_type
              if premise_ids:
                constraints_learned += 1
                constraints_learned_core += constraint_id in active_set
              if (extract_core and constraint_id in active_set) or\
                 (self.proof_type == constraint_type):
                self.constraints[constraint_id] = constraint
                self.premises[constraint_id] = premise_ids
                self.constraint_type[constraint_id] = constraint_type
                if attributes:
                  self.attribute_names = attributes[::2]
                if constraint_id in active_set:
                  self.constraint_in_core[constraint_id] = 1
                  for premise_id in premise_ids:
                    active_set.add(premise_id)
                else:
                  self.constraint_in_core[constraint_id] = 0
          if not file_position:
            break
    print("Number of constraints: {}".format(constraints_processed))
    if extract_core:
      print("Core size: {} ({:.2f})".format(
          len(self.constraints),
          len(self.constraints)/constraints_total))
    self.percentage_learned_core = constraints_learned_core/constraints_learned
    
    self.max_qdepth = 0
    for quantifier_line in reversed(quantifier_lines):
      self.readQuantifierBlock(quantifier_line)
      
  def outputAnnotated(self, filename):
    if self.attribute_names is not None:
      active_type = self.constraint_type[self.final_constraint_id]
      with open(self.filename) as trace, open(filename, 'w+') as outfile:
        outfile.write("{},{},{}\n".format(",".join(self.attribute_names),
                                          "Type",
                                          "Core"))
        for line in trace:
          if line.startswith(COMMENT_TOKEN):
            continue
          elif line.startswith(FORALL_TOKEN) or line.startswith(EXISTS_TOKEN):
            continue
          else:
            result = self.readTraceLine(line)
            constraint_id, constraint_type, constraint, premise_ids, attributes = result
            if constraint_type is active_type and premise_ids and constraint:
              outfile.write("{},{},{}\n".format(
                    ",".join(attributes[1::2]),
                    constraint_type,
                    int(constraint_id in self.constraints)))

  def readQuantifierBlock(self, line):
    qblock_string_split = line.split()
    assert qblock_string_split[-1] == EOL_TOKEN
    qblock_string_split = qblock_string_split[:-1]
    qtype, *variables = qblock_string_split
    for v in variables:
      self.qdepth[v] = self.max_qdepth
      self.qtype[v] = qtype
    self.max_qdepth += 1

  def readTraceLine(self, line):
    line_split = line.split()
    constraint_id, constraint_type, *rest = line_split
    try:
      constraint_id = int(constraint_id)
      constraint_type = int(constraint_type)
    except ValueError:
      assert False, line
    assert END_CONSTRAINT_TOKEN in rest, "No END_CONSTRAINT_TOKEN in rest of line: {}".format(line)
    constraint = rest[:rest.index(END_CONSTRAINT_TOKEN)]
    rest = rest[rest.index(END_CONSTRAINT_TOKEN)+1:]
    assert EOL_TOKEN in rest, "No EOL Token in rest of line: {}".format(line)
    premise_ids = [int(id) for id in rest[:rest.index(EOL_TOKEN)]]
    attributes = rest[rest.index(EOL_TOKEN)+1:]
    return constraint_id, constraint_type, constraint, premise_ids, attributes
  
  def printConstraint(qrp_id, constraint, premise_qrp_ids, qrp_file):
    premises_string = list(map(str, premise_qrp_ids))
    tokens = [str(qrp_id)] + constraint + [END_CONSTRAINT_TOKEN] + premises_string + [EOL_TOKEN]
    qrp_file.write(" ".join(tokens) + '\n')
    
  def printInputConstraint(self, constraint_id, qrp_file):
    self.id2id[constraint_id] = self.running_qrp_id
    self.running_qrp_id += 1
    TraceParser.printConstraint(self.id2id[constraint_id],
                                self.constraints[constraint_id], 
                                [],
                                qrp_file)
    
  def resolvent(self, first_constraint, second_constraint, constraint_type):
    pivot_type = FORALL_TOKEN if constraint_type else EXISTS_TOKEN
    clash = {var(l) for l in first_constraint if neg(l) in second_constraint}
    clash_pivot_type = {v for v in clash if self.qtype[v] == pivot_type}      
    assert len(clash_pivot_type) == 1
    pivot = clash_pivot_type.pop()
    assert all([self.qdepth[v] >= self.qdepth[pivot] for v in clash])
    result = ([l for l in first_constraint if var(l) != pivot] +
              [l for l in second_constraint if var(l) != pivot])
    return list(set(result))
  
  def reduct(self, constraint, constraint_type):
    sorted_constraint = sorted(constraint,
                               key=lambda l: self.qdepth[var(l)])
    reduced_type = EXISTS_TOKEN if constraint_type else FORALL_TOKEN
    while (sorted_constraint and
           self.qtype[var(sorted_constraint[-1])] == reduced_type):
      sorted_constraint.pop()
    return sorted_constraint
    
  def printDerivation(self, constraint_id, qrp_file):
    premise_ids = self.premises[constraint_id]
    constraint_type = self.constraint_type[constraint_id]
    conflict_constraint_id, *side_constraint_ids = premise_ids
    running_constraint = self.constraints[conflict_constraint_id]
    running_constraint_id = self.id2id[conflict_constraint_id]
    # Apply reduction to the conflict constraint.
    reduct = self.reduct(running_constraint, constraint_type)
    if len(reduct) < len(running_constraint):
      TraceParser.printConstraint(self.running_qrp_id,
                                    reduct,
                                    [running_constraint_id],
                                    qrp_file)
      running_constraint_id = self.running_qrp_id
      self.running_qrp_id += 1
      running_constraint = reduct
      
    for premise_id in side_constraint_ids:
      premise = self.constraints[premise_id]
      resolvent = self.resolvent(running_constraint, premise, constraint_type)
      TraceParser.printConstraint(self.running_qrp_id,
                                  resolvent,
                                  [running_constraint_id,
                                   self.id2id[premise_id]],
                                   qrp_file)
      running_constraint_id = self.running_qrp_id
      self.running_qrp_id += 1
      reduct = self.reduct(resolvent, constraint_type)
      if len(reduct) < len(resolvent):
        TraceParser.printConstraint(self.running_qrp_id,
                                    reduct,
                                    [running_constraint_id],
                                    qrp_file)
        running_constraint_id = self.running_qrp_id
        self.running_qrp_id += 1
      running_constraint = reduct
      
    self.id2id[constraint_id] = running_constraint_id
    assert set(reduct) <= set(self.constraints[constraint_id])
  
  def toQRP(self, filename):
    with open(filename, 'w+') as qrp_file:
      max_var_index = max([int(v) for v in self.qtype])
      qrp_file.write("p qrp {} 0\n".format(max_var_index)) #Print QRP header.
      # Next, print the quantifier prefix.
      for i in range(self.max_qdepth):
        variables_block = [v for v in self.qdepth if self.qdepth[v] == i]
        assert variables_block
        qtype = self.qtype[variables_block[0]]
        block_tokens = [qtype] + variables_block + [EOL_TOKEN]
        qrp_file.write(" ".join(block_tokens) + '\n')
      # Now for constraints.
      """ We want to assign contiguous IDs to QRP constraints.
          Since we're going to have to introduce new intermediate constraints,
          we cannot expect learned constraints to keep their original IDs.
          We use a dictionary to map old IDs to QRP IDs.
      """
      self.running_qrp_id = 1
      self.id2id = {}
  
      for constraint_id in sorted(self.premises):
        if not self.premises[constraint_id]:
          self.printInputConstraint(constraint_id, qrp_file)
        else:
          self.printDerivation(constraint_id, qrp_file)
  
      # Final constraint must be empty.
      assert len(self.constraints[constraint_id]) == 0
      result_string = "SAT" if self.constraint_type[constraint_id] else "UNSAT"
      qrp_file.write("r {}\n".format(result_string))
      
  def toIndexSet(self):
    variables = {var(l) for c in self.constraints.values() for l in c}
    variables_dict = {name:i for i, name in enumerate(variables)}
    nr_variables = len(variables)
    nr_constraints = len(self.constraints)
    idx = []
    targets = []
    for j, constraint_id in enumerate(self.constraints):
      targets.append(self.constraint_in_core[constraint_id])
      assert j < nr_constraints, "Index: {}, Constraints: {}".format(j, nr_constraints)
      c_indices = [[j, variables_dict[var(l)] + is_negated(l) * nr_variables]
                   for l in self.constraints[constraint_id]]
      idx += c_indices
    return nr_variables, nr_constraints, idx, targets
  
      
  def countUnique(self):
    clause_count = 0
    clauses = set()
    term_count = 0
    terms = set()
    
    for constraint_id in self.constraints:
      constraint = frozenset(self.constraints[constraint_id])
      if self.constraint_type[constraint_id] == 0:
        clause_count += 1
        clauses.add(constraint)
      else:
        term_count += 1
        terms.add(constraint)
    print("{} unique clauses ({}%)".format(len(clauses), 
                                           100*len(clauses)/clause_count))
    print("{} unique terms ({:.2f}%)".format(len(terms),
                                             100*len(terms)/term_count))
      