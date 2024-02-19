def my_comp(α β γ : Type) :(β → γ) -> (α → β ) -> (α → γ)
/-| g, f => g ∘ f-/
| g, f => λ a => g (f a )

def comp4 {α : Type}: (α → α) → (α → α)
| f => λ a => (f ∘ f ∘ f ∘ f) a


/- lamba is function type..its takes argument a and returns what the function has to do -/


/-what if u want to do n number of compositions,
so, this function takes 2 arguments, fist is n (Nat ) and second is function -/
def compn {α : Type} : Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| (Nat.succ n')  ,f => (λ a => f (compn n' f a))


def compni {α: Type}: Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| Nat.succ n', f => λ a =>  (f ∘ compni n' f) a

/-or here we can use the -/
def compnii {α: Type}: Nat → (α → α) → (α → α)
| Nat.zero, f => λ a => a
| Nat.succ n', f => (f ∘ compni n' f)


#eval (compn 5 Nat.succ) 0
#eval (compni 5 Nat.succ) 0

def sq (n:Nat) := n*n
#eval (compn 2 sq) 2
/-here nat.succ is a function which adds 1-/
/-write a square function which takes n -/

/-Inductive is keyword used to define a type-/

#check (@List)

/-!inductive List (α : Type u) where
  | nil : List α

  | cons (head : α) (tail : List α) : List α
-/
def e : List Nat := List.nil
def e' : List Nat := []

def l1 : List Nat := List.cons 1 e

#reduce l1

def l2: List Nat := List.cons 0 l1

#reduce l2

def list_len {α : Type} : List α → Nat
| List.nil => 0
| (List.cons h t) => 1+list_len t

#eval list_len l2
