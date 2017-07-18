import data.hash_map library_dev.data.list.set

namespace state

@[inline] def modify {σ : Type} : (σ → σ) → state σ unit :=
λ f s, ((), f s)

def inc : state ℕ unit := modify (λ n, n + 1)
def dec : state ℕ unit := modify (λ n, n - 1)
end state

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

inductive instruction : Type
| iconst : ℕ → instruction
| iget   : ℕ → instruction
| iset   : ℕ → instruction
| iadd   : instruction
| isub   : instruction
| imul   : instruction
| ibf    : ℕ → instruction
| ibb    : ℕ → instruction
| ibeq   : ℕ → instruction
| ibne   : ℕ → instruction
| ible   : ℕ → instruction
| ibgt   : ℕ → instruction
| ihalt  : instruction

open instruction

@[reducible] def code := list instruction.

@[reducible] def stack : Type := list ℕ
@[reducible] def config : Type := ℕ × stack

inductive veval (c : code) : config -> config -> Prop
| vconst : ∀ pc stk n, at_nth c pc (iconst n) → veval (pc, stk) (pc + 1, n :: stk)
| vget   : ∀ pc stk n v, at_nth c pc (iget n) → at_nth stk n v → veval (pc, stk) (pc + 1, v :: stk)
| vset   : ∀ pc stk n v stk', at_nth c pc (iset n) → set_nth stk n v = some stk' → veval (pc, v :: stk) (pc + 1, stk')
| vadd   : ∀ pc stk n n₁ n₂, at_nth c pc iadd → n = n₁ + n₂ → veval (pc, n₂ :: n₁ :: stk) (pc + 1, n :: stk)
| vsub   : ∀ pc stk n₁ n₂, at_nth c pc iadd → veval (pc, n₂ :: n₁ :: stk) (pc + 1, (n₁ - n₂) :: stk)
| vmul   : ∀ pc stk n₁ n₂, at_nth c pc iadd → veval (pc, n₂ :: n₁ :: stk) (pc + 1, (n₁ * n₂) :: stk)
| vbf    : ∀ pc stk ofs pc', at_nth c pc (ibf ofs) → pc' = (pc + ofs) + 1 → veval (pc, stk) (pc', stk)
| vbb    : ∀ pc stk ofs pc', at_nth c pc (ibf ofs) → pc' + ofs = pc + 1 → veval (pc, stk) (pc', stk)
| vbeq   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibeq ofs) → pc' = (if n₁ = n₂ then (pc + ofs) + 1 else pc + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| vbne   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibne ofs) → pc' = (if n₁ = n₂ then pc + 1 else (pc + ofs) + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| vble   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ible ofs) → pc' = (if n₁ ≤ n₂ then (pc + ofs) + 1 else pc + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| vbgt   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibgt ofs) → pc' = (if n₁ ≤ n₂ then pc + 1 else (pc + ofs) + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)

def vhalts (c : code) (stk_init stk_fin : stack) : Prop :=
∃ pc, at_nth c pc ihalt ∧ star (veval c) (0, stk_init) (pc, stk_fin)

def collect_assigned_vars : com → list var
| (cskip)       := []
| (cass v _)    := [v]
| (cseq c₁ c₂)  := collect_assigned_vars c₁ ∪ collect_assigned_vars c₂
| (cif b c₁ c₂) := collect_assigned_vars c₁ ∪ collect_assigned_vars c₂
| (cwhile b c)  := collect_assigned_vars c

@[reducible] def stack_offsets : Type := hash_map var (λ v : var, ℕ)

def compute_stack_offsets_core : list var → stack_offsets → stack_offsets
| []        s := s
| (v :: vs) s := compute_stack_offsets_core vs (s^.insert v (length vs))

def compute_stack_offsets (c : com) : stack_offsets :=
compute_stack_offsets_core (collect_assigned_vars c) (mk_hash_map (λ (v : var), v^.id))

-- TODO(dhs): not sure if this is the best way to do it
def agree (offsets : stack_offsets) (vofs : ℕ) (st : vstate) (stk : stack) : Prop :=
  ∀ (v : var), st^.dfind v = dnth stk (offsets^.dfind v + vofs)

lemma agree_push {offsets : stack_offsets} {vofs : ℕ} {st : vstate} {stk : stack} {n : ℕ} :
  agree offsets vofs st stk → agree offsets (vofs + 1) st (n :: stk) := sorry

inductive codeseq_at : code → ℕ → code → Prop
| intro : ∀ code₁ code₂ code₃ pc, pc = length code₁ → codeseq_at (code₁ ++ code₂ ++ code₃) pc code₂

def compile_aexp_core (offsets : stack_offsets) : aexp → ℕ → code
| (aexp.aconst n)   vofs := [iconst n]
| (aexp.avar v)     vofs := [iget $ offsets^.dfind v + vofs]
| (aexp.aadd e₁ e₂) vofs := compile_aexp_core e₂ vofs ++ compile_aexp_core e₁ (vofs + 1) ++ [iadd]
| (aexp.asub e₁ e₂) vofs := compile_aexp_core e₂ vofs ++ compile_aexp_core e₁ (vofs + 1) ++ [isub]
| (aexp.amul e₁ e₂) vofs := compile_aexp_core e₂ vofs ++ compile_aexp_core e₁ (vofs + 1) ++ [imul]

def compile_aexp (offsets : stack_offsets) (e : aexp) := compile_aexp_core offsets e 0

-- TODO(dhs): weaken the forall?
def astack_contains_vars (offsets : stack_offsets) : stack → ℕ → aexp → Prop
| stk vofs (aexp.aconst n)   := true
| stk vofs (aexp.avar v)     := offsets^.dfind v + vofs < length stk
| stk vofs (aexp.aadd e₁ e₂) := astack_contains_vars stk vofs e₂ ∧ ∀ x, astack_contains_vars (x :: stk) (vofs + 1) e₁
| stk vofs (aexp.asub e₁ e₂) := astack_contains_vars stk vofs e₂ ∧ ∀ x, astack_contains_vars (x :: stk) (vofs + 1) e₁
| stk vofs (aexp.amul e₁ e₂) := astack_contains_vars stk vofs e₂ ∧ ∀ x, astack_contains_vars (x :: stk) (vofs + 1) e₁

lemma compile_aexp_core_correct :
  ∀ code st e pc stk offsets vofs,
    codeseq_at code pc (compile_aexp_core offsets e vofs)
    → agree offsets vofs st stk
    → astack_contains_vars offsets stk vofs e
    → star (veval code) (pc, stk) (pc + length (compile_aexp_core offsets e vofs), aeval st e :: stk)

| .(_) st (aexp.aconst n) .(pc) stk offsets vofs (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_astack :=
begin
simp [compile_aexp_core, length, aeval],
apply star.rtrans,
apply veval.vconst,
apply at_nth_of_len H_pc,
apply star.rfl
end

| .(_) st (aexp.avar v) .(pc) stk offsets vofs (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_astack :=
begin
simp [compile_aexp_core, length, aeval],
apply star.rtrans,
apply veval.vget,
apply at_nth_of_len H_pc,
simp [agree] at H_agree,
simp [astack_contains_vars] at H_astack,
rw H_agree,
apply at_nth_of_dnth_lt H_astack,
apply star.rfl
end

| .(_) st (aexp.aadd e₁ e₂) .(pc) stk offsets vofs (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_astack :=
begin
simp [compile_aexp_core, length, aeval],
apply star.trans,
-- Compile e₂
apply compile_aexp_core_correct _ st e₂ _ _ offsets vofs _ H_agree (and.left H_astack),
rw ← append_assoc,
apply codeseq_at.intro _ _ _ _ H_pc,
-- Compile e₁
apply star.trans,
apply compile_aexp_core_correct _ st e₁ _ _ offsets (vofs+1) _ (agree_push H_agree) (and.right H_astack _),
have H_assoc :
(code₁ ++ (compile_aexp_core offsets e₂ vofs ++ (compile_aexp_core offsets e₁ (vofs + 1) ++ iadd :: code₃)))
=
(code₁ ++ compile_aexp_core offsets e₂ vofs) ++ (compile_aexp_core offsets e₁ (vofs + 1)) ++ iadd :: code₃ := sorry,
rw H_assoc, clear H_assoc,
apply codeseq_at.intro _ _ _ _,
simp [H_pc, length_append],

-- Add instruction
apply star.rtrans,
have H_assoc :
code₁ ++ (compile_aexp_core offsets e₂ vofs ++ (compile_aexp_core offsets e₁ (vofs + 1) ++ iadd :: code₃))
=
(code₁ ++ compile_aexp_core offsets e₂ vofs ++ compile_aexp_core offsets e₁ (vofs + 1)) ++ [iadd] ++ code₃ := sorry,
rw H_assoc, clear H_assoc,

have H_one_at_end :
pc + (1 + (length (compile_aexp_core offsets e₂ vofs) + length (compile_aexp_core offsets e₁ (vofs + 1))))
=
(pc + length (compile_aexp_core offsets e₂ vofs) + length (compile_aexp_core offsets e₁ (vofs + 1))) + 1 := sorry,
rw H_one_at_end, clear H_one_at_end,
apply veval.vadd,

have H_cons :
code₁ ++ compile_aexp_core offsets e₂ vofs ++ compile_aexp_core offsets e₁ (vofs + 1) ++ [iadd] ++ code₃
=
(code₁ ++ compile_aexp_core offsets e₂ vofs ++ compile_aexp_core offsets e₁ (vofs + 1)) ++ (iadd :: code₃) := sorry,
rw H_cons, clear H_cons,
apply at_nth_of_len,
simp [H_pc, length_append],
simp,
apply star.rfl,

end

def compile_bexp (offsets : stack_offsets) : bexp → bool → ℕ → code
| (bexp.btrue)      cond ofs := if cond then [ibf ofs] else []
| (bexp.bfalse)     cond ofs := if cond then [] else [ibf ofs]
| (bexp.bnot b)     cond ofs := compile_bexp b (bnot cond) ofs
| (bexp.band b₁ b₂) cond ofs := let code₂ := compile_bexp b₂ cond ofs,
                                    code₁ := compile_bexp b₁ false (if cond then length code₂ else ofs + length code₂)
                                in  code₁ ++ code₂

| (bexp.beq e₁ e₂)  cond ofs := compile_aexp_core offsets e₂ 0 ++ compile_aexp_core offsets e₁ 1 ++ (if cond then [ibeq ofs] else [ibne ofs])
| (bexp.ble e₁ e₂)  cond ofs := compile_aexp_core offsets e₂ 0 ++ compile_aexp_core offsets e₁ 1 ++ (if cond then [ible ofs] else [ibgt ofs])

-- TODO(dhs): weaken the forall?
-- TODO(dhs): is this even right? We'll see soon.
def bstack_contains_vars (offsets : stack_offsets) : stack → bexp → Prop
| stk (bexp.btrue)      := true
| stk (bexp.bfalse)     := true
| stk (bexp.bnot b)     := bstack_contains_vars stk b
| stk (bexp.band b₁ b₂) := bstack_contains_vars stk b₂ ∧ bstack_contains_vars stk b₁
| stk (bexp.beq e₁ e₂)  := astack_contains_vars offsets stk 0 e₂ ∧ ∀ x, astack_contains_vars offsets (x::stk) 1 e₁
| stk (bexp.ble e₁ e₂)  := astack_contains_vars offsets stk 0 e₂ ∧ ∀ x, astack_contains_vars offsets (x::stk) 1 e₁

--set_option pp.all true
--set_option trace.type_context.is_def_eq true
--set_option trace.type_context.is_def_eq_detail true

lemma compile_bexp_correct :
  ∀ code st b cond ofs pc stk offsets,
    codeseq_at code pc (compile_bexp offsets b cond ofs)
    → agree offsets 0 st stk
    → bstack_contains_vars offsets stk b
    → star (veval code) (pc, stk)
                        (pc + (length (compile_bexp offsets b cond ofs) + ite (beval st b = cond) ofs 0), stk)
/-
| .(_) st (bexp.btrue) cond ofs .(pc) stk offsets (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_bstack :=
begin
simp [compile_bexp, compile_aexp_core, length, aeval, beval],
cases cond,
{ simp, apply star.rfl },
simp,
apply star.rtrans,
apply veval.vbf _ _ ofs,
apply at_nth_of_len H_pc,
simp,
apply star.rfl
end

| .(_) st (bexp.bfalse) cond ofs .(pc) stk offsets (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_bstack :=
begin
simp [compile_bexp, compile_aexp_core, length, aeval, beval],
cases cond,
{ simp, apply star.rtrans, apply veval.vbf _ _ ofs, apply at_nth_of_len H_pc, simp, apply star.rfl },
{ simp, apply star.rfl },
end
-/

| .(_) st (bexp.bnot b) cond ofs .(pc) stk offsets (codeseq_at.intro code₁ ._ code₃ pc H_pc) H_agree H_bstack :=
begin
simp [compile_bexp, compile_aexp_core, length, aeval, beval],
-- TODO(dhs): come on, Lean
have H_bnot : ∀ beq, (@ite (bnot (beval st b) = cond) beq _ ofs 0) = (ite (beval st b = bnot cond) ofs 0) := sorry,
rw H_bnot, clear H_bnot,

apply compile_bexp_correct (code₁ ++ (compile_bexp offsets b (bnot cond) ofs ++ code₃)) st b (bnot cond) ofs pc stk offsets _ H_agree H_bstack,
rw ← append_assoc,
apply codeseq_at.intro _ _ _ _ H_pc,

end
/-

  forall C st b cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (transition C)
       (pc, stk, st)
       (pc + length (compile_bexp b cond ofs) + if eqb (beval st b) cond then ofs else 0, stk, st).
-/
#exit
-- Example program
---------------------------
-- (cass `x 1)
-- (cass `y (+ x x))
-- (cass `z (+ x (+ y x))

-- Want
--------------------------
-- Initial stack: [x:=0, y:=0, z:=0]
-- cass `x 1 ==>  push 1, iset 1 ==> [x:=1, y:=0, z:=0]
-- cass `y (+ x x) ==> iget 0, iget 1, iadd, iset 2 ==> [x:=2, y:=4, z:=0]
-- cass `z (+ x (+ y x)) ==> iget 0, iget 2, iget 2, iadd, iadd, iset 3

definition compile_com (offsets : stack_offsets) : com → code
| cskip         := []
| (cass v e)    := compile_aexp offsets e ++ [iset $ offsets^.dfind v]
| (cseq c₁ c₂)  := compile_com c₁ ++ compile_com c₂

| (cif b c₁ c₂) := let code₁ := compile_com c₁,
                       code₂ := compile_com c₂
                   in  compile_bexp offsets b false (length code₁ + 1) ++ code₁ ++ [ibf (length code₂)] ++ code₂
| (cwhile b c)  := let code_body := compile_com c,
                       code_test := compile_bexp offsets b ff (length code_body + 1)
                   in  code_test ++ code_body ++ [ibb (length code_test + length code_body + 1)]


-- TODO(dhs): is this _strong_ enough, with `offsets` an argument?
-- TODO(dhs): is this _weak_ enough, to prove?
theorem compile_correct_terminating_alt :
  ∀ code st c st',
    ceval c st st' →
      ∀ offsets stk pc, codeseq_at code pc (compile_com offsets c) →
                agree offsets st stk →
                ∃ stk', star (veval code) (pc, stk) (pc + length (compile_com offsets c), stk')
                        ∧ agree offsets st' stk'
| code ._ ._ ._ (eskip st) :=
begin
simp [compile_com, length],
intros offsets stk pc H_codeseq H_agree,
apply exists.intro stk,
split,
exact H_agree,
apply star.rfl
end

| code ._ ._ ._ (eass st a n x H_aeval) :=
begin
simp [compile_com, length],
intros offsets stk pc H_codeseq H_agree,

end

| code ._ ._ ._ (eseq c₁ c₂ st₁ st₂ st₃ H_c₁ H_c₂) :=
begin

end

| code ._ ._ ._ (eift st₁ st₂ b c₁ c₂ H_beval_t H_ceval₁) :=
begin

end

| code ._ ._ ._ (eiff st₁ st₂ b c₁ c₂ H_beval_f H_ceval₂) :=
begin

end

| code ._ ._ ._ (ewhilet st₁ st₂ st₃ b c H_beval_t H_ceval_step H_ceval_loop) :=
begin

end

| code ._ ._ ._ (ewhilef st b c H_beval_f) :=
begin

end

end compiler
