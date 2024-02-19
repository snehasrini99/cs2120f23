/-Q, P are propositions- asserting that a fact is true-/
/-! A proposition is true only if there is a proof-/
/-! Operations that can be done on propositions
P and Q
P or Q
P is equivalent to Q
not P
-/

/- P implies Q Truth table-/

0 0 1
1 0 0
0 1 1
1 1 1

/-if false is on the left--- the final answer will always be true-/



#check Empty
def e2e: Empty → Empty
| e => e
