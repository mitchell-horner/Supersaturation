import Mathlib

open Finset Fintype

namespace SimpleGraph

section ExtremalNumber

variable {n : ℕ} {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The extremal number on `n` vertices is at most `n.choose 2`. -/
theorem extremalNumber_le_choose_two : extremalNumber n H ≤ n.choose 2 := by
  rw [← Fintype.card_fin n, extremalNumber_le_iff]
  exact fun _ _ _ ↦ card_edgeFinset_le_card_choose_two

end ExtremalNumber

end SimpleGraph
