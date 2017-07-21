import data.hash_map .atom

namespace nominal
open list

inductive exp : Type
| var : atom → exp
| const : ℕ → exp
| abs : atom → exp → exp
| app : exp → exp → exp

open exp

def fvs : exp → list atom
| (var v)     := [v]
| (const n)   := []
| (abs v e)   := remove_all (fvs e) [v]
| (app e₁ e₂) := fvs e₁ ∪ fvs e₂

def swap_var (x y z : atom) : atom :=
  if z = x then y else if z = y then x else z.

def swap (x y : atom) : exp → exp
| (var z)     := var (swap_var x y z)
| (const n)   := const n
| (abs z e)   := abs (swap_var x y z) (swap e)
| (app e₁ e₂) := app (swap e₁) (swap e₂)

@[reducible] def heap := hash_map atom (λ x, exp)
structure frame := (val : exp)
def stack := list frame

structure config := (hp : heap) (t : exp) (stk : stack)

inductive step (α : Type) : Type
| error {}  : step
| done  {}  : exp → step
| take      : α → step

def machine_step (avoid : list atom) : config → step config
| ⟨hp, abs x e, []⟩ := step.done (abs x e)

| ⟨hp, abs x e, (⟨val⟩ :: stk)⟩ :=
 if x ∈ hp ∨ x ∈ avoid
 then let y := atom.fresh (hp^.keys ∪ avoid) in step.take ⟨hp^.insert y val, swap x y e, stk⟩
 else step.take ⟨hp^.insert x val, e, stk⟩

| ⟨hp, var x, stk⟩ := match hp^.find x with
                     | some e := step.take ⟨hp, e, stk⟩
                     | none   := step.error
                     end

| ⟨hp, app f a, stk⟩ := step.take ⟨hp, f, ⟨a⟩ :: stk⟩


| ⟨hp, const n, stk⟩ := step.done (const n)

def init_config (t : exp) : config := ⟨mk_hash_map (λ a : atom, a^.id), t, []⟩

def is_val : exp → Prop
| (abs _ _) := true
| _         := false

lemma values_are_done (avoid : list atom) : ∀ (t : exp), is_val t → machine_step avoid (init_config t) = step.done t
| (abs x e) _ := rfl
| (const n) _ := rfl
| (var v) H_contra := false.rec _ H_contra
| (app f a) H_contra := false.rec _ H_contra

def size : exp → ℕ
| (var x) := 1
| (const n) := 1
| (abs x e) := 1 + size e
| (app f a) := 1 + size f + size a

lemma swap_size_eq (x y : atom) : ∀ t, size (swap x y t) = size t :=
begin
intro t,
induction t,
reflexivity,
all_goals { simp [swap, size], try { cc } }
end

/-
inductive exp : Type
| var : atom → exp
| const : ℕ → exp
| abs : atom → exp → exp
| app : exp → exp → exp
-/
open exp

inductive result : Type
| error   : string → result
| done    : exp → result
| nofuel  : exp → result

def reduce (avoid : list atom) : ℕ → config → result
| 0     ⟨hp, e, stk⟩       := result.nofuel e
| (t+1) ⟨hp, abs x e, []⟩  := result.done (abs x e)
| (t+1) ⟨hp, const n, stk⟩ := result.done (const n)

| (t+1) ⟨hp, abs x e, (⟨val⟩ :: stk)⟩ :=
 if x ∈ hp ∨ x ∈ avoid
 then let y := atom.fresh (hp^.keys ∪ avoid) in reduce t ⟨hp^.insert y val, swap x y e, stk⟩
 else reduce t ⟨hp^.insert x val, e, stk⟩

| (t+1) ⟨hp, var x, stk⟩ :=
 match hp^.find x with
 | some e := reduce t ⟨hp, e, stk⟩
 | none   := result.error "variable not found"
 end

| (t+1) ⟨hp, app f a, stk⟩ := reduce t ⟨hp, f, ⟨a⟩ :: stk⟩

example : reduce [] 10 (init_config $ app (abs ⟨0⟩ (var ⟨0⟩)) (const 5)) = result.done (const 5) :=
begin
simp [reduce, init_config, hash_map.not_contains_empty, has_mem.mem, list.mem, hash_map.find_insert],
end



end nominal
