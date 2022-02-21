Assume prefix order. Clauses and initial terms are already reduced (?).

Use first two literals as initial watchers.

1) Two existentials.
Upon assignment, look for another existential.
If there is no existential, try to find a non-falsified universal the other watcher depends on.
If that does not exist, the clause is unit, propagate (make sure propagated literal is clause[0]).

2) One existential, one universal.
  a) Universal gets assigned. Try to find a non-falsified existential. 
  If none exists, another non-falsified universal the existential watcher depends on. If none, propagate existential.

  Corner case for 1) and 2a): what if there is a universal literal satisfying the clause that the existential watcher does not depend on?
  Do not propagate, do not change watchers.

  b) Existential gets assigned. Find another non-falsified existential.
  
  Again, if there is a true universal (existential as well?) literal, leave both watchers as they are.
  If none exists, the clause is falsified.
  Otherwise, there are two cases:

     I) There is a non-falsified existential that depends on the universal watcher.
    II) The existential does *not* depend on the universal.