import data.hash_map

namespace nominal
open list

structure atom := (id : nat)
namespace atom
instance : decidable_eq atom := by tactic.mk_dec_eq_instance

end atom

def fresh_atom_core : list atom → ℕ → atom
| [] next_id := ⟨next_id⟩
| (atom::atoms) next_id := fresh_atom_core atoms (max atom^.id next_id)

def fresh_atom (atoms : list atom) : atom := fresh_atom_core atoms 0

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

def heap := hash_map atom (λ x, exp)
structure frame := (val : exp)
def stack := list frame

structure config := (hp : heap) (t : exp) (stk : stack)

inductive step (α : Type) : Type
| error {} : step
| done  {} : step
| take     : α → step

def machine_step (avoid : list atom) : config → step config
| ⟨hp, abs x e, []⟩ := step.done

| ⟨hp, abs x e, (⟨val⟩ :: stk)⟩ :=
 if x ∈ hp^.keys ∪ avoid
 then let y := fresh_atom (hp^.keys ∪ avoid) in step.take ⟨hp^.insert y val, swap x y e, stk⟩
 else step.take ⟨hp^.insert x val, e, stk⟩

| ⟨hp, var x, stk⟩ := match hp^.find x with
                     | some e := step.take ⟨hp, e, stk⟩
                     | none   := step.error
                     end

| ⟨hp, app f a, stk⟩ := step.take ⟨hp, f, ⟨a⟩ :: stk⟩

def init_config (t : exp) : config := ⟨mk_hash_map (λ a : atom, a^.id), t, []⟩

def is_val : exp → Prop
| (abs _ _) := true
| _         := false

lemma values_are_done (avoid : list atom) : ∀ (t : exp), is_val t → machine_step avoid (init_config t) = step.done
| (abs x e) _ := rfl
| (var v) H_contra := false.rec _ H_contra
| (app f a) H_contra := false.rec _ H_contra

def size : exp → ℕ
| (var x) := 1
| (abs x e) := 1 + size e
| (app f a) := 1 + size f + size a

lemma swap_size_eq (x y : atom) : ∀ t, size (swap x y t) = size t :=
begin
intro t,
induction t,
reflexivity,
all_goals { simp [swap, size], cc }
end





end nominal
