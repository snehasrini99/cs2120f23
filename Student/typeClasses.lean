structure functor'' (c: Type → Type) where
map {α β: Type} (f: α → β) (ic: c α) : c β


def do_map' {α β : Type} {c : Type → Type} (m : functor'' c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

inductive Box (α : Type)
| contents (a : α)

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

def list_functor : functor'' List  := functor''.mk list_map
def option_functor : functor'' Option  := functor''.mk option_map

#eval do_map' list_functor Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map' option_functor (λ s => s ++ "!") (some "Hi")

class functor (c: Type → Type) where
map {α β: Type} (f: α → β) (ic: c α) : c β


/-! USe square brackets -/

def do_map {α β : Type} {c : Type → Type} [m : functor c] :
  (f : α → β) → c α → c β
| f, c => m.map f c


/-!
there is  a problem
-/
#reduce do_map Nat.succ [1,2,3]


/-! We need to register Typeclass instances-/


instance: functor List := ( list_map )
instance: functor Box := ( box_map )

#reduce do_map Nat.succ [1,2,3]


infix:50 "<$>"  => do_map
#eval Nat.succ <$> [1,2,3]
#eval do_map Nat.succ [1,2,3]
#eval (λ s => s ++ "!") <$> ["Hi", "Yo"]
