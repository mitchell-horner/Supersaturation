import Mathlib

namespace Finset

open Function Multiset

section powersetCard

variable {α : Type*} {s t : Finset α} {n : ℕ}

/-- The number of `n`-sized subsets of `s` that contain `t` is `(#s - #t).choose (n - #t)`. -/
theorem card_filter_powersetCard_superset [DecidableEq α] (h : t ⊆ s) (hn : #t ≤ n) :
    #{ u ∈ powersetCard n s | t ⊆ u } = (#s - #t).choose (n - #t) := by
  rw [← card_sdiff_of_subset h, ← card_powersetCard]
  refine card_bij' (fun u _ ↦ u \ t) (fun u _ ↦ u ∪ t)
      (fun u hu ↦ ?_) (fun u hu ↦ ?_) (by simp) (fun u hu ↦ ?_)
  · rw [mem_filter, mem_powersetCard] at hu
    rw [mem_powersetCard]
    exact ⟨sdiff_subset_sdiff hu.1.1 subset_rfl, by rw [card_sdiff_of_subset hu.2, hu.1.2]⟩
  · rw [mem_powersetCard, subset_sdiff] at hu
    rw [mem_filter, mem_powersetCard]
    refine ⟨⟨union_subset hu.1.1 h, ?_⟩, subset_union_right⟩
    rw [card_union_of_disjoint hu.1.2, hu.2, Nat.sub_add_cancel hn]
  · rw [mem_powersetCard, subset_sdiff] at hu
    simpa [union_sdiff_right] using hu.1.2.sdiff_eq_left

end powersetCard

end Finset
