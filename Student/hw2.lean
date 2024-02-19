/-Write a function called add that takes two natural numbers, a and b, and returns their sum, a + b.
Don't just look up the answer. Figure it out on your own. Hint: do case analysis on
the second argument (a Nat can be either Nat.zero or (Nat.succ n') and use the fact that n + (1 + m) = 1 + (n + m).-/

def add(a:Nat)(b:Nat) := a+b

def add3 : Nat → Nat → Nat
| n, 0 => n
| n, (m'+1) => Nat.add 1 (add3 n m')

def mul: Nat -> Nat → Nat
| n, 0 => 0
| n, (m'+1) => add n (mul n m')

#eval mul 1 3

def exp: Nat → Nat → Nat
| n,0 => 1
| n,m'+1 => mul n (exp n m')


def add2: Nat -> Nat -> Nat
| Nat.zero, m => m
| n, Nat.zero => n
| Nat.succ n' , Nat.succ m' =>  Nat.succ (add2 (n') m'+1)

/-ff-/

def listadd  : List  -> List  -> List
| a.cons 0 1, b.cons 0 1 => List.nil

#eval add2 2 3
#check Bool

/-!
inductive Bool : Type where
  | false : Bool
  | true : Bool
-/

#check Unit

/-!
Induction Unit :Type where
| unit: PUnit
-/

#check Empty
 def e2e : EMpty → Empty|
