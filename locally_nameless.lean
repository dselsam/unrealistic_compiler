import .atom data.hash_map

namespace locally_nameless

inductive type : Type
| base : type
| arrow : type → type → type

inductive exp : Type
| var_b : ℕ → exp
| var_f : atom → exp
| const : ℕ → exp
| abs   : exp → exp
| app   : exp → exp → exp

open exp

def subst_exp (v:atom) (s:exp) : exp → exp
| (var_b n)   := var_b n
| (var_f x)   := if x = v then s else var_f x
| (const n)  := const n
| (abs e)     := abs (subst_exp e)
| (app e₁ e₂) := app (subst_exp e₁) (subst_exp e₂)

def fv_exp : exp → list atom
| (var_b nat) := []
| (var_f x)   := [x]
| (const n)   := []
| (abs e)     := fv_exp e
| (app e₁ e₂) := fv_exp e₁ ∪ fv_exp e₂

def open_exp_wrt_exp_core : ℕ → exp → exp → exp
| k s (var_b n) := match has_ordering.cmp n k with
               | ordering.lt  := var_b n
               | ordering.eq  := s
               | ordering.gt  := var_b (n-1)
               end

| k s (var_f x)   := var_f x
| k s (const n)   := const n
| k s (abs e)     := abs (open_exp_wrt_exp_core (k+1) s e)
| k s (app e₁ e₂) := app (open_exp_wrt_exp_core k s e₁) (open_exp_wrt_exp_core k s e₂)


def open_exp_wrt_exp (s e : exp) : exp := open_exp_wrt_exp_core 0 s e.

def context : Type := hash_map atom (λ a, exp)

def reduce : exp → option exp
| (app (abs f) a) := have exp.sizeof (open_exp_wrt_exp a f) < exp.sizeof f + (exp.sizeof a + 2), from sorry, reduce (open_exp_wrt_exp a f)
| (abs e)         := some (abs e)
| (const n)       := some (const n)
| (app _ _)       := none
| (var_b n)       := none
| (var_f v)       := none

#check @reduce.equations._eqn_1
#check @reduce.equations._eqn_2
#check @reduce.equations._eqn_3
#check @reduce.equations._eqn_4
#check @reduce.equations._eqn_5
#check @reduce.equations._eqn_6
#check @reduce.equations._eqn_7
#check @reduce.equations._eqn_8

lemma not_lt_refl : ∀ (n : ℕ), ¬ (n < n) := sorry

example : reduce (app (abs (var_b 0)) (const 5)) = some (const 5) :=
begin
simp [reduce, open_exp_wrt_exp, open_exp_wrt_exp_core, open_exp_wrt_exp_core._match_1, has_ordering.cmp, nat.cmp, not_lt_refl],
end



end locally_nameless
