/-!Your homework, due before class on Wednesday, is to complete the
definition of the general foldr function, with the
reduction of lists of strings to Boolean values
as a test case, true if every string in a list is of
even length, and false otherwise. Your foldr function must
be completely general and not test-case specific,
however the function that we are calling "combine" will be
application/test-case specific. To do the homework,
complete the following
definitions by replacing the underscores with your own code.-/
def isEvenLen : String → Bool := λ s => s.length % 2 == 0

#eval isEvenLen "popp"

def combine : String → Bool → Bool := λ a b => isEvenLen a && b == true
#eval combine "popp" true



def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#eval foldr combine true  ["ll","pp"]



def foldr1 {α: Type} : (α → α → α) → α → List α → α
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

#eval foldr1 Nat.add 0 [1,2,3]


#eval foldr1 Nat.add 1 [1,2,3]

/-! Here identity element given is wrong-/
/-!
What can go wrong
You can  pass a non identity element.
-/
/-! What rules must be enforced?
- id is the identity elemt for op
-
-/


structure my_monoid (α : Type) where
(op: α → α → α)
(id: α)
(left_id: ∀ (a: α), op id a = a)
(right_id: ∀ (a: α), op a id = a)

def a_monoid: my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check
