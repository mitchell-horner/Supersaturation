import Mathlib
import Supersaturation.Combinatorics.SimpleGraph.Extremal.Basic

open Filter Finset Fintype

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem turanDensity_le_extremalNumber_div_choose_two (H : SimpleGraph W) {n : ℕ} (hn : n ≥ 2) :
    turanDensity H ≤ extremalNumber n H / n.choose 2 := by
  rw [turanDensity_eq_csInf H]
  exact csInf_le (isGLB_turanDensity H).bddBelow ⟨n, hn, rfl⟩

theorem turanDensity_nonneg (H : SimpleGraph W) : 0 ≤ turanDensity H := by
  rw [turanDensity_eq_csInf]
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ ↦ ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  · rw [← hx]
    positivity

/-- There are at least `card W` many vertices at `turanDensityConst`, since simple graphs on
fewer vertices cannot contain `H`. -/
theorem card_le_turanDensityConst [Fintype W] (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    (h : H.turanDensity + ε ≤ 1) : card W ≤ turanDensityConst H ε := by classical
  rw [turanDensityConst, dif_pos hε_pos, Nat.le_find_iff]
  intro m hm hp
  obtain ⟨f⟩ := by
    apply hp m le_rfl (G := (⊤ : SimpleGraph (Fin m)))
    rw [card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin, ge_iff_le]
    exact mul_le_of_le_one_left (Nat.cast_nonneg _) h
  have : card W ≤ m := by simpa using Fintype.card_le_of_embedding f.toEmbedding
  omega

theorem turanDensity_le_one (H : SimpleGraph W) : turanDensity H ≤ 1 := by
  rw [turanDensity_eq_csInf]
  apply csInf_le_of_le (isGLB_turanDensity H).bddBelow ⟨2, le_refl 2, rfl⟩
  rw [div_le_iff₀ (mod_cast Nat.choose_pos le_rfl), one_mul, Nat.cast_le]
  exact extremalNumber_le_choose_two

end SimpleGraph
