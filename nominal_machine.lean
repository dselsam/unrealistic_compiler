namespace nominal
open list

structure atom := (id : nat)
namespace atom
instance : decidable_eq atom := by tactic.mk_dec_eq_instance
end atom

inductive exp : Type
| var : atom → exp
| abs : atom → exp → exp
| app : exp → exp → exp

open exp

def fvs : exp → list atom
| (var v)     := [v]
| (abs v e)   := remove_all (fvs e) [v]
| (app e₁ e₂) := fvs e₁ ∪ fvs e₂

def swap_var (x y z : atom) : atom :=
  if z = x then y else if z = y then x else z.

def swap (x y : atom) : exp → exp
| (var z)     := var (swap_var x y z)
| (abs z e)   := abs (swap_var x y z) (swap e)
| (app e₁ e₂) := app (swap e₁) (swap e₂)

end nominal
