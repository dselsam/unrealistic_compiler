structure atom := (id : nat)
namespace atom
instance : decidable_eq atom := by tactic.mk_dec_eq_instance

def fresh_atom_core : list atom → ℕ → atom
| [] next_id := ⟨next_id⟩
| (atom::atoms) next_id := fresh_atom_core atoms (max atom^.id next_id)

def fresh (atoms : list atom) : atom := fresh_atom_core atoms 0

end atom
