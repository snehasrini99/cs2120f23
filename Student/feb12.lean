structure monoid' (α: Type ) where
(op: α → α → α)
(id: α)

def foldr {α : Type} : monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr m t)

#eval foldr (monoid'.mk Nat.add 0) [1,2,3,4]

#eval foldr (monoid'.mk String.append "") ["hi", " hola"]

#eval foldr (monoid'.mk Nat.mul 1) [1,2,3]

/-!
what does a monoid do

it extends a binary operator to be a n-ary opertaor.

A group is a monoid but has an additional operator called reverse
-/

structure my_monoid (α : Type) where
(op: α → α → α)
(id: α)
(left_id: ∀ a, op id a =a)
(right_id: ∀ a, op a id =a)
(op_assoc: ∀ a b c, op a (op b c)= op (op a b) c)

def foldr' {α : Type} : my_monoid α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)

def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr' nat_add_monoid [1,2,3]


def nat_add_monoid' : my_monoid Nat :=
( Nat.add,
  0,
λ a => by simp [Nat.add],
λ a => by simp [Nat.add],
Nat.add_assoc
)


def nat_mul_monoid'' : my_monoid Nat :=
  (Nat.mul,
  1,
  λ a => by simp,
  λ a => by simp,
  Nat.mul_assoc )

  def nary_mul' :List Nat → Nat  := foldr' (my_monoid.mk Nat.mul 1 sorry sorry sorry)

#eval nary_mul' [1,2,3]

/-!
Another mathematical structure fuctor-/

#check (@Option)

def pred: Nat → Option Nat
| Nat.zero => Option.none
| Nat.succ a => a

#reduce pred 3


/-! partial functions-/
def option_map {α β: Type} : (α → β ) → Option α → Option β
| f, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-! if alpha is none it returns none-/


def list_map {α β : Type}: (α → β) → List α → List β
|_, [] =>[]
|f, h::t => f h :: list_map f t

inductive Tree (α: Type): Type
| empty
| node: α → Tree α → Tree α → Tree α
/-! or define it like this
|node (a: α) (l r : Tree α): Tree α
-/

def tree_map {α β : Type}: (α → β) → Tree α → Tree β
| _, Tree.empty => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

/-!Constructing a Tree-/
def a_tree:=
  Tree.node
  1
  (Tree.node
  2
  Tree.empty
  Tree.empty)
  (Tree.node
  3
  Tree.empty
  Tree.empty)


  #reduce tree_map Nat.succ a_tree



  /-! here we cant do paramteric polymorphism
  because the implementation  of the part which is not empty is
  different-/

  /-! adhoc polymorphism - -/

  /-! List has a type: Type to type-/
  /-! Tree has a type: Type to type-/
  /-! Option has a type: Type to type-/

  /-! defining a new functor-/


/-! here c can be a tree list or option-/
structure functor {α β : Type} (c: Type → Type): Type where
map (f: α → β) (ic: c α): (c β)

/-! Take a a container of alpha and returns container of beta-/

-- def list_functor{α β: Type}: functor List Nat.succ := functor.mk list_map
-- def option_functor{α β: Type}: functor Option Nat.succ := functor.mk option_map

def list_functor {α β : Type}: @functor α β List := functor.mk list_map
def option_functor {α β : Type}: @functor α β Option := functor.mk list_map

def convert {α β : Type} (c: Type → Type) (m: @functor α β c) : (f: α → β)  → c α → c β
| f, c => m.map f c

#reduce convert List list_functor Nat.succ [1,2,3,4]
#reduce convert Option option_functor Nat.succ (Option.some 4)

inductive Box (α : Type)
| contents (a : α)
#reduce convert
