/-!
#1

Define a function, dec' : Nat → Nat, that takes any Nat, n, and that
returns 0 if n is 0 and that otherwise returns one less than n. Hint:
case analysis on n. When you've succeeded the following test cases
should run and return the expected values.
-/
def dec': Nat → Nat
| Nat.zero => Nat.zero
| n'+1 => n'

/-thh-/
def dec'2 : Nat → Nat
| Nat.zero => 0
| 1 => 0
| (Nat.succ (Nat.succ n') ) => n'



#eval dec' 2    -- expect 1
#eval dec' 1    -- expect 0
#eval dec' 0    -- expect 0

/-
#2

Define a function, l2l, polymorphic in two type parameters, α and β, that
also takes a function, f, from α to β and a list of α values and that returns
a  list of corresponding β values. As an example, (l2l Nat.succ [0, 1, 2]) is
expected to return [1, 2, 3]. Write a few test cases where α is String, β is
Nat, and f is String.length. Hint: Use case analysis on the incoming list: it
will be either List.nil or (List.cons h t), the latter of which can also be
written as (h::t).
-/

-- def l2l(α β : Type): (α → β) -> (List α )-> (List β)
-- |  _, List.nil => []
-- | f, List.cons h t  => List.cons (f h ) (l2l f t)

def l2l {α β : Type}: (α → β) -> (List α )-> (List β)
| _, List.nil => []
| f, h::t => f h :: (l2l f t)

/-! list l [1,2,3] can be written as 1::2::3::nil-/
/-!
#3

Define a data type, called PRFV (short for "partial function return value"),
polymorphic in one type, α, where a value of this type is either "undefined"
or "defined α". If α is Nat, for example, then you would have (undefined) and
(defined 3) as values of this type. In the case of undefined,, you will have
to disable implicit arguments, as there's no value provided to this constructor
from which Lean can infer α.
-/


/- use curly braces when u want to infer the type lean implicitly -/
-- inductive PRFV {α : Type} : Type
-- | undefined : PRFV
-- | defined : α → PRFV


inductive PRFV (α : Type)
| undefined
| defined (a : α)

def p1 : PRFV Nat := PRFV.undefined
def p2 := PRFV.defined 1



-- #check @PRFV.undefined     -- expect PRFV
-- #check PRFV.defined 3         -- Expect PRFV

/-!
#4

Define a variant of dec', called dec, that takes a natural number, n, as an
argument and that returns a (PRFV Nat). This value must be "PFRV.undefined"
if n = 0, reflecting the idea that dec is a partial function, one that is not
defined for the argument value, 0; and that returns one less than n otherwise.
You will thus represent a partial function from Nat to Nat as a total function
from Nat to PRFV Nat.
-/

def dec : Nat → PRFV Nat
| Nat.zero => PRFV.undefined
| Nat.succ n' => PRFV.defined n'

#reduce dec 2

/-!
#5

Define a function, isZero from Nat to Bool that returns true if its argument
is zero and false otherwise. Write a few test cases to show that it works.
-/

def isZero: Nat → Bool
| Nat.zero => true
| Nat.succ m' => false

#eval isZero 0
#eval isZero 1

/-!
#6

Define a function, isDef, from PFRV α to Bool, that returns false if the given
PFRV α is "undefined" and true otherwise. The following test cases should then
return the expected values.
-/

def isDef: PRFV Nat → Bool
| (PRFV.undefined )  => false
| (PRFV.defined Nat)  => true

#eval isDef (dec 0)   -- expect false
#eval isDef (dec 1)   -- expect true


/-! fold right function-/
/-add numbers in list-/
def fold : (Nat → Nat → Nat) →Nat → List Nat → Nat
| op, id , List.nil => id
| op, id, h::t => op h (fold op id t)

#reduce fold Nat.add 0 [1,2,3,4]
#reduce fold Nat.mul 1 [1,2,3,4]


def folds : (String → String → String) → String → List String → String
| op, id ,List.nil => id
| op, id, h::t => op h (folds op id t)

#eval folds String.append "" ["hello", "World"]


def foldnew {α : Type}: (α → α → α) → α → List α → α
| op, id ,List.nil => id
| op, id, h::t => op h (foldnew op id t)


-- def combine : (String → Bool → Bool) :=
-- /-!reduce a list of string to bool true if all strings in have even lenght-/

-- def foldbool  {α β : Type}: (α → β → β)→ β → List α → β
-- | op, id, List.nil => List.nil
-- | op, id, h::t => op h ()


-- def isEvenLen : String → Bool := λ s => s.length % 2 == 0

-- #eval isEvenLen "popp"

-- def combine : String → Bool → Bool := λ a b => isEvenLen a == true
-- #eval combine "popp" true



-- def foldr {α β : Type} : (α → β → β) → β → List α → β
-- | _, id, List.nil => id
-- | op, id, (h::t) => op h (foldr op id t)

-- #eval foldr combine true  ["ll","ppp"]
