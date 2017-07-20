import data.hash_map library_dev.data.list.set

universe u

namespace list

def dnth {α : Type*} [decidable_eq α] [inhabited α] (xs : list α) (n : ℕ) : α :=
match xs^.nth n with
| (some x) := x
| none     := default α
end

def at_nth {α : Type*} (xs : list α) (idx : ℕ) (x : α) : Prop := nth xs idx = some x

def set_nth {α : Type*} : list α → ℕ → α → option (list α)
| (x::xs) 0     a := some (a :: xs)
| (x::xs) (i+1) a := do ys ← set_nth xs i a, return (x :: ys)
| []      _     _ := none

instance decidable_subset {α : Type*} [decidable_eq α] (xs ys : list α) : decidable (xs ⊆ ys) :=
begin
simp [has_subset.subset, list.subset],
apply_instance
end

lemma at_nth_of_dnth_lt {α : Type*} [decidable_eq α] [inhabited α] {xs : list α} {idx : ℕ} :
  idx < length xs → at_nth xs idx (dnth xs idx) := sorry

lemma at_nth_of_len {α : Type*} {xs ys : list α} {x : α} {k : ℕ} : k = length xs → at_nth (xs ++ x :: ys) k x := sorry

end list

namespace hash_map

def dfind {α : Type*} [decidable_eq α] {β : α → Type*} [∀ a, inhabited (β a)] (m : hash_map α β) (a : α) : β a :=
match m^.find a with
| (some b) := b
| none     := default (β a)
end

end hash_map

def hash_set (α : Type u) [decidable_eq α] : Type u :=
hash_map α (λ x : α, unit)

namespace hash_set

variables {α : Type u} [decidable_eq α]

def insert (s : hash_set α) (x : α) : hash_set α :=
hash_map.insert s x ()

def contains (s : hash_set α) (x : α) : bool :=
(hash_map.find s x).is_some

instance : has_mem α (hash_set α) := ⟨λa m, m.contains a⟩

end hash_set

section seq
variables {α : Type*} (rel : α → α → Prop)

inductive star : α → α → Prop
| rfl    : ∀ (x : α), star x x
| rtrans : ∀ (x y z : α), rel x y → star y z → star x y

end seq

namespace star
variables {α : Type*} (rel : α → α → Prop)

lemma trans (x y z : α) : star rel x y → star rel y z → star rel x z := sorry

end star

namespace compiler
open tactic list

structure var : Type := (id : ℕ)

namespace var
instance : decidable_eq var := by mk_dec_eq_instance
end var

@[reducible] def vstate : Type := hash_map var (λ v : var, ℕ)
def empty_vstate : vstate := mk_hash_map (λ v : var, v^.id)

inductive aexp : Type
| aconst : ℕ → aexp
| avar   : var → aexp
| aadd   : aexp → aexp → aexp
| asub   : aexp → aexp → aexp
| amul   : aexp → aexp → aexp

inductive bexp : Type
| btrue  : bexp
| bfalse : bexp
| bnot   : bexp → bexp
| band   : bexp → bexp → bexp
| beq    : aexp → aexp → bexp
| ble    : aexp → aexp → bexp

def aeval (st : vstate) : aexp → ℕ
| (aexp.aconst n) := n
| (aexp.avar v) := st^.dfind v
| (aexp.aadd e₁ e₂) := aeval e₁ + aeval e₂
| (aexp.asub e₁ e₂) := aeval e₁ - aeval e₂
| (aexp.amul e₁ e₂) := aeval e₁ * aeval e₂

def beval (st : vstate) : bexp → bool
| (bexp.btrue)      := tt
| (bexp.bfalse)     := ff
| (bexp.bnot b)     := bnot (beval b)
| (bexp.band b₁ b₂) := beval b₁ && beval b₂
| (bexp.beq e₁ e₂)  := aeval st e₁ = aeval st e₂
| (bexp.ble e₁ e₂)  := aeval st e₁ ≤ aeval st e₂

inductive com : Type
| cskip  : com
| cass   : var → aexp → com
| cseq   : com → com → com
| cif    : bexp → com → com → com
| cwhile : bexp → com → com

open com

inductive ceval : com → vstate → vstate → Prop
| eskip : ∀ st, ceval cskip st st
| eass  : ∀ st a n x, aeval st a = n → ceval (cass x a) st (st^.insert x n)
| eseq : ∀ c₁ c₂ st₁ st₂ st₃, ceval c₁ st₁ st₂ → ceval c₂ st₂ st₃ → ceval (cseq c₁ c₂) st₁ st₃
| eift : ∀ st₁ st₂ b c₁ c₂, beval st₁ b = tt → ceval c₁ st₁ st₂ → ceval (cif b c₁ c₂) st₁ st₂
| eiff : ∀ st₁ st₂ b c₁ c₂, beval st₁ b = ff → ceval c₂ st₁ st₂ → ceval (cif b c₁ c₂) st₁ st₂
| ewhilet : ∀ st₁ st₂ st₃ b c, beval st₁ b = tt → ceval c st₁ st₂ → ceval (cwhile b c) st₂ st₃ → ceval (cwhile b c) st₁ st₃
| ewhilef : ∀ st b c, beval st b = ff → ceval (cwhile b c) st st

open ceval

def fv_aexp : aexp → list var
| (aexp.aconst n) := []
| (aexp.avar v)   := [v]
| (aexp.aadd e₁ e₂) := fv_aexp e₁ ∪ fv_aexp e₂
| (aexp.asub e₁ e₂) := fv_aexp e₁ ∪ fv_aexp e₂
| (aexp.amul e₁ e₂) := fv_aexp e₁ ∪ fv_aexp e₂

def fv_bexp : bexp → list var
| (bexp.btrue)      := []
| (bexp.bfalse)     := []
| (bexp.bnot b)     := fv_bexp b
| (bexp.band b₁ b₂) := fv_bexp b₁ ∪ fv_bexp b₂
| (bexp.beq e₁ e₂)  := fv_aexp e₁ ∪ fv_aexp e₂
| (bexp.ble e₁ e₂)  := fv_aexp e₁ ∪ fv_aexp e₂

def fv_com : com → list var
| cskip         := []
| (cass x e)    := fv_aexp e
| (cseq c₁ c₂)  := fv_com c₁ ∪ fv_com c₂
| (cif b c₁ c₂) := fv_bexp b ∪ fv_com c₁ ∪ fv_com c₂
| (cwhile b c)  := fv_bexp b ∪ fv_com c

section fixpoint

parameter (F : list var → list var)
parameter (dflt : list var)

def iterate : ℕ → list var → list var
| 0     _ := dflt
| (n+1) x := let x' := F x in (if x' ⊆ x then x else iterate n x')

lemma iterate_charact : ∀ (niter : ℕ) (start : list var), F (iterate niter start) ⊆ (iterate niter start) ∨ (iterate niter start) = dflt
| 0           _     := or.inr rfl
| (niter + 1) start :=
begin
simp only [iterate],
have H_em : F start ⊆ start ∨ ¬ (F start ⊆ start) := decidable.em _,
cases H_em with H_ss H_n_ss,
{ simp only [H_ss, if_pos, if_simp_congr], left, triv },
{ simp only [H_n_ss, if_neg, if_simp_congr, if_false], apply iterate_charact }
end

def fixpoint : list var := iterate 10 []

lemma fixpoint_charact : (F fixpoint ⊆ fixpoint) ∨ (fixpoint = dflt) :=
by apply iterate_charact

variable (F_stable : ∀ x, x ⊆ dflt → F x ⊆ dflt)
include F_stable

lemma iterate_upper_bound : ∀ (niter : ℕ) (start : list var), start ⊆ dflt → iterate niter start ⊆ dflt
| 0         start := by { simp [iterate] }
| (niter+1) start :=
begin
simp [iterate],
have H_em : F start ⊆ start ∨ ¬ (F start ⊆ start) := decidable.em _,
cases H_em with H_ss H_n_ss,
{ simp [H_ss], intro H, exact H },
{ simp [H_n_ss], intro H, apply iterate_upper_bound, exact F_stable _ H }
end

lemma fixpoint_upper_bound : fixpoint ⊆ dflt :=
begin
apply iterate_upper_bound,
exact F_stable,
apply nil_subset
end

end fixpoint



end compiler
