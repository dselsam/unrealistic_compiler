import data.hash_map

universe u

namespace tactic

meta def at_target (tac : expr → tactic (expr × expr)) : tactic unit :=
  do tgt ← target,
     (new_tgt, pf) ← tac tgt,
     n ← mk_fresh_name,
     assert n new_tgt, swap,
     ht ← get_local n,
     mk_app `eq.mpr [pf, ht] >>= exact

meta def fsimpt (ns : list name) (tac : tactic unit) : tactic unit := do
  s ← list.mfoldl (λ slss n, simp_lemmas.add_simp slss n) simp_lemmas.mk ns,
  at_target (λ e, do (a, new_e, pf) ← ext_simplify_core () {} s
                                                        (λ u, failed)
                                                        (λ a s r p e, failed)
                                                        (λ a s r p e, do ⟨u, new_e, pr⟩ ← conv.apply_lemmas_core s tac r e,
                                                                         return ((), new_e, pr, tt))
                                                        `eq e,
                     return (new_e, pf))
end tactic
namespace list
variable {α : Type u}

def dnth [decidable_eq α] [inhabited α] (xs : list α) (n : ℕ) : α :=
match xs^.nth n with
| (some x) := x
| none     := default α
end

def at_nth (xs : list α) (idx : ℕ) (x : α) : Prop := nth xs idx = some x

def set_nth : list α → ℕ → α → option (list α)
| (x::xs) 0     a := some (a :: xs)
| (x::xs) (i+1) a := do ys ← set_nth xs i a, return (x :: ys)
| []      _     _ := none

instance decidable_subset [decidable_eq α] (xs ys : list α) : decidable (xs ⊆ ys) :=
begin
simp [has_subset.subset, list.subset],
apply_instance
end

lemma subset_trans [decidable_eq α] {xs zs : list α} (ys : list α) : xs ⊆ ys → ys ⊆ zs → xs ⊆ zs := sorry
lemma subset_union_left [decidable_eq α] (xs ys zs : list α) : xs ⊆ ys → xs ⊆ ys ∪ zs := sorry
lemma subset_union_right [decidable_eq α] (xs ys zs : list α) : xs ⊆ zs → xs ⊆ ys ∪ zs := sorry

lemma subset_pre_union_left [decidable_eq α] {xs ys zs : list α} : xs ∪ ys ⊆ zs → xs ⊆ zs := sorry
lemma subset_pre_union_right [decidable_eq α] {xs ys zs : list α} : xs ∪ ys ⊆ zs → ys ⊆ zs := sorry

lemma subset_union_trans_right [decidable_eq α] {xs ys zs} (ws : list α) : zs ⊆ ws → xs ⊆ ys ∪ zs → xs ⊆ ys ∪ ws := sorry
lemma subset_union_trans_left [decidable_eq α] {xs ys zs} (ws : list α) : ys ⊆ ws → xs ⊆ ys ∪ zs → xs ⊆ ws ∪ zs := sorry

lemma remove_all_subset [decidable_eq α] (xs ys zs : list α) : xs ⊆ zs → remove_all xs ys ⊆ zs := sorry

lemma at_nth_of_dnth_lt [decidable_eq α] [inhabited α] {xs : list α} {idx : ℕ} :
  idx < length xs → at_nth xs idx (dnth xs idx) := sorry

lemma at_nth_of_len {xs ys : list α} {x : α} {k : ℕ} : k = length xs → at_nth (xs ++ x :: ys) k x := sorry

lemma mem_of_singleton_subset [decidable_eq α] -- TODO(dhs): current spot
H_ss : [v] ⊆ L
⊢ v ∈ L

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


/- Liveness analysis. -/

/- [L] is the set of variables live "after" command [c].
  The result of [live c L] is the set of variables live "before" [c]. -/

def live : com → list var → list var
| cskip         L := L
| (cass x e)    L := if x ∈ L then remove_all L [x] else fv_aexp e
| (cseq c₁ c₂)  L := live c₁ (live c₂ L)
| (cif b c₁ c₂) L := fv_bexp b ∪ live c₁ L ∪ live c₂ L
| (cwhile b c)  L := let L' := fv_bexp b ∪ L,
                         dflt := fv_com (cwhile b c) ∪ L
                     in  fixpoint (λ x, L' ∪ live c x) dflt

lemma live_upper_bound : ∀ (c : com) (L : list var), live c L ⊆ fv_com c ∪ L
| cskip         L :=
begin
simp [live],
apply subset_union_right, apply subset.refl
end

| (cass x e)    L :=
begin
simp [live, fv_com],
have H_em : x ∈ L ∨ ¬ (x ∈ L) := decidable.em _,
cases H_em with H_mem H_nmem,
{ simp [H_mem], apply subset_union_right, apply remove_all_subset, apply subset.refl },
{ simp [H_nmem], apply subset_union_left, apply subset.refl }
end

| (cseq c₁ c₂)  L :=
begin
simp [live, fv_com],
have H₁ : live c₂ L ⊆ fv_com c₂ ∪ L := by apply live_upper_bound,
have H₂ : live c₁ (live c₂ L) ⊆ fv_com c₁ ∪ live c₂ L := by apply live_upper_bound,
exact sorry -- TODO(dhs): simple but missing lemmas
end

| (cif b c₁ c₂) L :=
begin
simp [live, fv_com],
exact sorry -- TODO(dhs): simple
end

| (cwhile b c)  L :=
begin
simp [live, fv_com],
apply fixpoint_upper_bound,
intros start H,
have H_suff : live c start ⊆ fv_com c ∪ L,
exact sorry, -- TODO(dhs): easy
exact sorry -- TODO(dhs): easy
end

lemma live_while_charact (b : bexp) (c : com) (L : list var) :
  let L' := live (cwhile b c) L in
  fv_bexp b ⊆  L' ∧ L ⊆ L' ∧ live c L' ⊆ L' :=
begin
dsimp,
have H := fixpoint_charact (λ xs, fv_bexp b ∪ L ∪ live c xs) (fv_bexp b ∪ fv_com c ∪ L),
cases H with H H,
split,
{ exact sorry },
{ exact sorry },
split,
{ simp [live, fv_com], rw H, apply subset_union_left, apply subset_union_left, apply subset.refl },
split,
{ simp [live, fv_com, H], apply subset_union_right, apply subset.refl  },
{ simp [live, fv_com, H], apply subset_trans, apply live_upper_bound, exact sorry } -- TODO(dhs): easy
end

/- 3. Dead code elimination -/

/- Code transformation -/

/- The code transformation turns assignments [x ::= a] to dead variables [x]
  into [SKIP] statements. -/

def dce : com → list var → com
| cskip         L := cskip
| (cass x e)    L := if x ∈ L then cass x e else cskip
| (cseq c₁ c₂)  L := cseq (dce c₁ (live c₂ L)) (dce c₂ L)
| (cif b c₁ c₂) L := cif b (dce c₁ L) (dce c₂ L)
| (cwhile b c)  L := cwhile b (dce c $ live (cwhile b c) L)

/- Semantic correctness -/

/- Two states agree on a set [L] of live variables if they assign
  the same values to each live variable. -/

def agree (L : list var) (st₁ st₂: vstate) : Prop :=
  ∀ x, x ∈ L → st₁^.dfind x = st₂^.dfind x

/- Monotonicity property. -/

lemma agree_monotonic (L L' : list var) (st₁ st₂ : vstate) :
  agree L' st₁ st₂ → L ⊆ L' → agree L st₁ st₂ :=
begin
simp [agree],
intros H H_ss x H_mem,
simp [H x (H_ss H_mem)]
end

/- Agreement on the free variables of an expression implies that this
    expression evaluates identically in both states. -/

lemma aeval_agree (L : list var) (st₁ st₂ : vstate) (H_agree : agree L st₁ st₂) :
  ∀ (e : aexp), fv_aexp e ⊆ L → aeval st₁ e = aeval st₂ e
| (aexp.aconst n) := λ H_ss, rfl

| (aexp.avar v)   :=
begin
simp [fv_aexp, aeval],
intro H_ss,
apply H_agree,
apply mem_of_subset
end

| (aexp.aadd e₁ e₂) :=
begin
simp [fv_aexp, aeval],
intro H_ss,
have H₁ : aeval st₁ e₁ = aeval st₂ e₁,
{ apply aeval_agree, exact subset_pre_union_left H_ss },
have H₂ : aeval st₁ e₂ = aeval st₂ e₂,
{ apply aeval_agree, exact subset_pre_union_right H_ss },
simp [H₁, H₂]
end

| (aexp.asub e₁ e₂) :=
begin
simp [fv_aexp, aeval],
intro H_ss,
have H₁ : aeval st₁ e₁ = aeval st₂ e₁,
{ apply aeval_agree, exact subset_pre_union_left H_ss },
have H₂ : aeval st₁ e₂ = aeval st₂ e₂,
{ apply aeval_agree, exact subset_pre_union_right H_ss },
simp [H₁, H₂]
end

| (aexp.amul e₁ e₂) :=
begin
simp [fv_aexp, aeval],
intro H_ss,
have H₁ : aeval st₁ e₁ = aeval st₂ e₁,
{ apply aeval_agree, exact subset_pre_union_left H_ss },
have H₂ : aeval st₁ e₂ = aeval st₂ e₂,
{ apply aeval_agree, exact subset_pre_union_right H_ss },
simp [H₁, H₂]
end

set_option pp.all true
set_option trace.simplify true

lemma beval_agree (L : list var) (st₁ st₂ : vstate) (H_agree : agree L st₁ st₂) :
  ∀ (b : bexp), fv_bexp b ⊆ L → beval st₁ b = beval st₂ b
| (bexp.btrue)      H_ss := rfl
| (bexp.bfalse)     H_ss := rfl
| (bexp.bnot b)     H_ss :=
begin
simp [beval], apply congr_arg, apply beval_agree, exact H_ss
end

| (bexp.band b₁ b₂) H_ss :=
begin
simp [fv_bexp] at H_ss,
simp [beval],
have H₁ : beval st₁ b₁ = beval st₂ b₁,
{ apply beval_agree, apply subset_pre_union_left H_ss },
have H₂ : beval st₁ b₂ = beval st₂ b₂,
{ apply beval_agree, apply subset_pre_union_right H_ss },
simp [H₁, H₂]
end

| (bexp.beq e₁ e₂)  H_ss :=
begin
simp [fv_bexp] at H_ss,
simp only [beval],
have H₁ : aeval st₁ e₁ = aeval st₂ e₁,
{ apply aeval_agree, exact H_agree, apply subset_pre_union_left H_ss },
have H₂ : aeval st₁ e₂ = aeval st₂ e₂,
{ apply aeval_agree, exact H_agree, apply subset_pre_union_right H_ss },
-- TODO(dhs): investigate crazy Lean behavior
simp only [H₁]
--rw [H₁, H₂]
end

| (bexp.ble e₁ e₂)  H_ss :=
begin
simp [fv_bexp] at H_ss,
simp [beval],
have H₁ : aeval st₁ e₁ = aeval st₂ e₁,
{ apply aeval_agree, exact H_agree, apply subset_pre_union_left H_ss },
have H₂ : aeval st₁ e₂ = aeval st₂ e₂,
{ apply aeval_agree, exact H_agree, apply subset_pre_union_right H_ss },
-- TODO(dhs): investigate crazy Lean behavior
-- simp only [H₁, H₂]
rw [H₁, H₂]
end

end compiler
