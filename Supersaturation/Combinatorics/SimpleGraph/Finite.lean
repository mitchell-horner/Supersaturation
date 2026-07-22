import Mathlib

open Finset Function

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]
  {e : Sym2 V} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem filter_edgeFinset_toFinset_subset (s : Finset V) :
    { e ∈ G.edgeFinset | e.toFinset ⊆ s } = G.edgeFinset ∩ s.sym2 := by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

/-- The edges whose vertices lie in `s` are in bijection with the edges of the induced
subgraph `G.induce s`. -/
theorem card_filter_edgeFinset_toFinset_subset (s : Finset V) :
    #{ e ∈ G.edgeFinset | e.toFinset ⊆ s } = #(G.induce ↑s).edgeFinset := by
  have h := congrArg Finset.card (map_edgeFinset_induce (s := (↑s : Set V)) (G := G))
  rw [card_map, toFinset_coe] at h
  rw [filter_edgeFinset_toFinset_subset]
  convert h.symm using 1
  congr!

end SimpleGraph
