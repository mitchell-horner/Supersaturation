import Mathlib

open Finset Function

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]
  {e : Sym2 V} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem filter_edgeFinset_toFinset_subset (s : Finset V) :
    { e ∈ G.edgeFinset | e.toFinset ⊆ s } = G.edgeFinset ∩ s.sym2 := by
  simp [subset_iff, ← mem_sym2_iff, filter_mem_eq_inter]

end SimpleGraph
