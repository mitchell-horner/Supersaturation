import Mathlib

open Finset Fintype Function

namespace SimpleGraph

variable {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {I : SimpleGraph X}

namespace Copy

/-- The copy of any simple graph in `⊤` that can embed its vertices. -/
protected def top (f : W ↪ V) : Copy H (⊤ : SimpleGraph V) :=
  ⟨⟨f, fun h ↦ f.injective.ne h.ne⟩, f.injective⟩

/-- The copy of `H` in `H.map ·`. -/
protected abbrev map (f : W ↪ V) : Copy H (H.map f) := (Embedding.map f H).toCopy

/-- The copy of `G.map ·` in `G`. -/
protected abbrev map' (f : V ≃ W) : Copy (G.map f) G := (Iso.map f G).symm.toCopy

/-- The copy of `G.comap ·` in `G`. -/
protected abbrev comap (f : W ↪ V) : Copy (G.comap f) G := (Embedding.comap f G).toCopy

/-- The copy of `H` in `H.comap ·`. -/
protected abbrev comap' (f : V ≃ W) : Copy H (H.comap f) := (Iso.comap f H).symm.toCopy

end Copy

section IsContained

lemma isContained_top_iff_card_le [Fintype V] [Fintype W] :
    H ⊑ (⊤ : SimpleGraph V) ↔ card W ≤ card V :=
  ⟨fun ⟨f⟩ ↦ Fintype.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.top (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.top := isContained_top_iff_card_le

end IsContained

section LabelledCopyCount

variable [Fintype V] [Fintype W] [Fintype X]

/-- Swap the `classical` fintype instance in `labelledCopyCount` for an explicit fintype
instance. -/
theorem labelledCopyCount_eq_card_copy [Fintype (Copy H G)] :
    G.labelledCopyCount H = card (Copy H G) := by
  rw [labelledCopyCount]
  convert rfl

/-- `labelledCopyCount` is invariant under isomorphism of the host graph. -/
theorem labelledCopyCount_congr_left (f : G ≃g H) :
    G.labelledCopyCount I = H.labelledCopyCount I := by
  classical simp_rw [labelledCopyCount_eq_card_copy, Fintype.card_eq]
  exact ⟨⟨fun c ↦ f.toCopy.comp c, fun c ↦ f.symm.toCopy.comp c,
    fun c ↦ by ext; simp, fun c ↦ by ext; simp⟩⟩

/-- `labelledCopyCount` is invariant under isomorphism of the copied graph. -/
theorem labelledCopyCount_congr_right (f : H ≃g I) :
    G.labelledCopyCount H = G.labelledCopyCount I := by
  classical simp_rw [labelledCopyCount_eq_card_copy, Fintype.card_eq]
  exact ⟨⟨fun c ↦ c.comp f.symm.toCopy, fun c ↦ c.comp f.toCopy,
    fun c ↦ by ext; simp, fun c ↦ by ext; simp⟩⟩

/-- The number of labelled copies of `⊥` in `G` is the number of injections from `W` to the
vertices of `G`. -/
theorem labelledCopyCount_bot (G : SimpleGraph V) :
    G.labelledCopyCount (⊥ : SimpleGraph W) = (card V).descFactorial (card W) := by classical
  rw [labelledCopyCount_eq_card_copy, ← Fintype.card_embedding_eq]
  exact Fintype.card_congr ⟨Copy.toEmbedding, Copy.bot, fun f ↦ Copy.ext fun w ↦ rfl, fun f ↦ rfl⟩

variable [DecidableEq V] [Fintype (Copy H G)]

omit [Fintype V] in
/-- The number of copies of `H` in the induced subgraph of `G` by `s` is equal to the number of
copies of `H` in `G` with vertices in `s`. -/
theorem labelledCopyCount_induce_eq_card_filter_copy (s : Finset V) :
    (G.induce s).labelledCopyCount H
      = #{f : Copy H G | univ.map f.toEmbedding ⊆ s} := by classical
  rw [labelledCopyCount_eq_card_copy]
  refine card_bij' (fun f _ ↦ (Copy.induce G s).comp f)
    (fun f hf ↦ ⟨⟨fun w ↦ ⟨f w, ((mem_filter_univ f).mp hf) <|
        mem_map_of_mem f.toEmbedding (mem_univ w)⟩, f.toHom.map_adj⟩,
      fun _ _ h ↦ f.injective (Subtype.val_inj.mpr h)⟩)
    (fun u hu ↦ by simp [subset_iff, Copy.induce, Copy.toEmbedding])
    (fun _ _ ↦ mem_univ _)
    (fun u hu ↦ by simp [Copy.ext_iff, Copy.induce])
    (fun u hu ↦ Copy.ext_iff.mpr (fun _ ↦ by rfl))

omit [Fintype V] in
/-- The number of copies of `H` in the induced subgraph of `G` by `s` is equal to the number of
copies of `H` in `G` with vertices in `s`. -/
theorem labelledCopyCount_induce_eq_card_subtype_copy (s : Finset V) :
    (G.induce s).labelledCopyCount H
      = card {f : Copy H G // univ.map f.toEmbedding ⊆ s} := by
  rw [labelledCopyCount_induce_eq_card_filter_copy,
    ← card_univ, ← subtype_univ, card_subtype]

omit [DecidableEq V] [Fintype (Copy H G)] in
theorem labelledCopyCount_induce_le (s : Finset V) :
    (G.induce s).labelledCopyCount H ≤ G.labelledCopyCount H := by classical
  rw [labelledCopyCount_induce_eq_card_subtype_copy, labelledCopyCount_eq_card_copy]
  exact card_subtype_le (fun f : Copy H G ↦ univ.map f.toEmbedding ⊆ s)

end LabelledCopyCount

end SimpleGraph
