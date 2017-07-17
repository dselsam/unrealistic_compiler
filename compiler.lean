import data.hash_map

open tactic list

namespace hash_map

def dfind {α : Type*} [decidable_eq α] {β : α → Type*} [∀ a, inhabited (β a)] (m : hash_map α β) (a : α) : β a :=
match m^.find a with
| (some b) := b
| none     := default (β a)
end

end hash_map

namespace compiler

structure var : Type := (id : ℕ)

namespace var
instance : decidable_eq var := by mk_dec_eq_instance
end var

def state : Type := hash_map var (λ v : var, ℕ)

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

def aeval (st : state) : aexp → ℕ
| (aexp.aconst n) := n
| (aexp.avar v) := st^.dfind v
| (aexp.aadd e₁ e₂) := aeval e₁ + aeval e₂
| (aexp.asub e₁ e₂) := aeval e₁ - aeval e₂
| (aexp.amul e₁ e₂) := aeval e₁ * aeval e₂

def beval (st : state) : bexp → bool
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

inductive ceval : com → state → state → Prop
| eskip : ∀ st, ceval cskip st st
| eass  : ∀ st a n x, aeval st a = n → ceval (cass x a) st (st^.insert x n)
| eseq : ∀ c₁ c₂ st₁ st₂ st₃, ceval c₁ st₁ st₂ → ceval c₂ st₂ st₃ → ceval (cseq c₁ c₂) st₁ st₃
| eift : ∀ st₁ st₂ b c₁ c₂, beval st₁ b = tt → ceval c₁ st₁ st₂ → ceval (cif b c₁ c₂) st₁ st₂
| eiff : ∀ st₁ st₂ b c₁ c₂, beval st₁ b = ff → ceval c₂ st₁ st₂ → ceval (cif b c₁ c₂) st₁ st₂
| ewhilet : ∀ st₁ st₂ st₃ b c, beval st₁ b = tt → ceval c st₁ st₂ → ceval (cwhile b c) st₂ st₃ → ceval (cwhile b c) st₁ st₃
| ewhilef : ∀ st b c, beval st b = ff → ceval (cwhile b c) st st

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

def code := list instruction.

@[reducible] def stack : Type := list ℕ
@[reducible] def config : Type := ℕ × stack

def at_nth {α : Type*} (xs : list α) (idx : ℕ) (x : α) : Prop := nth xs idx = some x

def set_nth {α : Type*} : list α → ℕ → α → option (list α)
| (x::xs) 0     a := some (a :: xs)
| (x::xs) (i+1) a := do ys ← set_nth xs i a, return (x :: ys)
| []      _     _ := none

inductive veval (c : code) : config -> config -> Prop
| trans_const : ∀ pc stk n, at_nth c pc (iconst n) → veval (pc, stk) (pc + 1, n :: stk)
| trans_get   : ∀ pc stk n v, at_nth c pc (iget n) → at_nth stk n v → veval (pc, stk) (pc + 1, v :: stk)
| trans_set   : ∀ pc stk n v stk', at_nth c pc (iset n) → set_nth stk n v = some stk' → veval (pc, v :: stk) (pc + 1, stk')
| trans_add   : ∀ pc stk n₁ n₂, at_nth c pc iadd → veval (pc, n₂ :: n₁ :: stk) (pc + 1, (n₁ + n₂) :: stk)
| trans_sub   : ∀ pc stk n₁ n₂, at_nth c pc iadd → veval (pc, n₂ :: n₁ :: stk) (pc + 1, (n₁ - n₂) :: stk)
| trans_mul   : ∀ pc stk n₁ n₂, at_nth c pc iadd → veval (pc, n₂ :: n₁ :: stk) (pc + 1, (n₁ * n₂) :: stk)
| trans_bf    : ∀ pc stk ofs pc', at_nth c pc (ibf ofs) → pc' = pc + 1 + ofs → veval (pc, stk) (pc', stk)
| trans_bb    : ∀ pc stk ofs pc', at_nth c pc (ibf ofs) → pc' + ofs = pc + 1 → veval (pc, stk) (pc', stk)
| trans_beq   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibeq ofs) → pc' = (if n₁ = n₂ then pc + 1 + ofs else pc + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| trans_bne   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibeq ofs) → pc' = (if n₁ = n₂ then pc + 1 else pc + 1 + ofs) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| trans_ble   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ible ofs) → pc' = (if n₁ ≤ n₂ then pc + 1 + ofs else pc + 1) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)
| trans_bgt   : ∀ pc stk ofs n₁ n₂ pc', at_nth c pc (ibgt ofs) → pc' = (if n₁ ≤ n₂ then pc + 1 else pc + 1 + ofs) → veval (pc, n₂ :: n₁ :: stk) (pc', stk)



end compiler
