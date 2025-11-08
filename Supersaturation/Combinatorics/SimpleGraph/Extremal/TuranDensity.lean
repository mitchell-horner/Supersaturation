import Mathlib
import Supersaturation.Combinatorics.SimpleGraph.Extremal.Basic

open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

-- TODO https://github.com/leanprover-community/mathlib4/pull/29449/files
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G := sorry

-- TODO https://github.com/leanprover-community/mathlib4/pull/29449/files
theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := sorry

-- TODO https://github.com/leanprover-community/mathlib4/pull/29449/files
theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } (turanDensity H) := sorry

theorem turanDensity_le_extremalNumber_div_choose_two (H : SimpleGraph W) {n : ℕ} (hn : n ≥ 2) :
    turanDensity H ≤ extremalNumber n H / n.choose 2 := by
  rw [turanDensity_eq_csInf H]
  exact csInf_le (isGLB_turanDensity H).bddBelow ⟨n, hn, rfl⟩

/-- The Turán density of a simple graph is at most one. -/
theorem turanDensity_le_one (H : SimpleGraph W) : turanDensity H ≤ 1 := by
  rw [turanDensity_eq_csInf]
  apply csInf_le_of_le (isGLB_turanDensity H).bddBelow ⟨2, le_refl 2, rfl⟩
  rw [div_le_iff₀ (mod_cast Nat.choose_pos le_rfl), one_mul, Nat.cast_le]
  exact extremalNumber_le_choose_two

end SimpleGraph
