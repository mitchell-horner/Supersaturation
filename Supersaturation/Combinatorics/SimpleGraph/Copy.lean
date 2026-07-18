import Mathlib

open Finset Fintype Function

namespace SimpleGraph

variable {α β γ : Type*} {A : SimpleGraph α} {B : SimpleGraph β} {C : SimpleGraph γ}

namespace Copy

/-- The copy of any simple graph in `⊤` that can embed its vertices. -/
protected def top (f : α ↪ β) : Copy A (⊤ : SimpleGraph β) :=
  ⟨⟨f, fun h ↦ f.injective.ne h.ne⟩, f.injective⟩

/-- The copy of `A` in `A.map ·`. -/
protected def map (f : α ↪ β) : Copy A (A.map f) :=
  ⟨⟨f, fun h ↦ by simp [h]⟩, f.injective⟩

/-- The copy of `A.map ·` in `A`. -/
protected def map' (f : α ≃ β) : Copy (A.map f) A :=
  ⟨⟨f.symm, fun hadj ↦ by simpa [← map_adj_apply (f := (f : α ↪ β))] using hadj⟩, f.symm.injective⟩

/-- The copy of `A.comap ·` in `A`. -/
protected def comap (f : β ↪ α) : Copy (A.comap f) A :=
  ⟨⟨f, fun h ↦ by simpa using h⟩, f.injective⟩

/-- The copy of `A` in `A.comap ·`. -/
protected def comap' (f : β ≃ α) : Copy A (A.comap f) :=
  ⟨⟨f.symm, fun h ↦ by simpa using h⟩, f.symm.injective⟩

end Copy

section IsContained

/-- `⊥` is contained in any simple graph having sufficiently many vertices. -/
lemma isContained_top_iff_card_le [Fintype α] [Fintype β] :
    A ⊑ (⊤ : SimpleGraph β) ↔ Fintype.card α ≤ Fintype.card β :=
  ⟨fun ⟨f⟩ ↦ Fintype.card_le_of_embedding f.toEmbedding,
    fun h ↦ ⟨Copy.top (Function.Embedding.nonempty_of_card_le h).some⟩⟩

protected alias IsContained.top := isContained_top_iff_card_le

end IsContained

section LabelledCopyCount

variable [Fintype α] [Fintype β] [Fintype γ]

/-- Swap the `classical` fintype instance in `labelledCopyCount` for an explicit fintype
instance. -/
theorem labelledCopyCount_eq_card_copy [Fintype (Copy B A)] :
    A.labelledCopyCount B = card (Copy B A) := by
  rw [labelledCopyCount]
  convert rfl

theorem labelledCopyCount_congr_left (f : A ≃g B) :
    A.labelledCopyCount C = B.labelledCopyCount C := by
  classical simp_rw [labelledCopyCount_eq_card_copy, Fintype.card_eq]
  exact ⟨⟨fun c ↦ f.toCopy.comp c, fun c ↦ f.symm.toCopy.comp c,
    fun c ↦ by ext; simp, fun c ↦ by ext; simp⟩⟩

theorem labelledCopyCount_congr_right (f : B ≃g C) :
    A.labelledCopyCount B = A.labelledCopyCount C := by
  classical simp_rw [labelledCopyCount_eq_card_copy, Fintype.card_eq]
  exact ⟨⟨fun c ↦ c.comp f.symm.toCopy, fun c ↦ c.comp f.toCopy,
    fun c ↦ by ext; simp, fun c ↦ by ext; simp⟩⟩

variable [DecidableEq α] [Fintype (Copy B A)]

omit [Fintype α] in
/-- The number of copies of `B` in the induced subgraph of `A` by `s` is equal to the number of
copies of `B` in `A` with vertices in `s`. -/
theorem labelledCopyCount_induce_eq_card_filter_copy (s : Finset α) :
    (A.induce s).labelledCopyCount B
      = #{f : Copy B A | univ.map f.toEmbedding ⊆ s} := by classical
  rw [labelledCopyCount_eq_card_copy]
  refine card_bij' (fun f _ ↦ (Copy.induce A s).comp f)
    (fun f hf ↦ ⟨⟨fun w ↦ ⟨f w, ((mem_filter_univ f).mp hf) <|
        mem_map_of_mem f.toEmbedding (mem_univ w)⟩, f.toHom.map_adj⟩,
      fun _ _ h ↦ f.injective (Subtype.val_inj.mpr h)⟩)
    (fun u hu ↦ by simp [subset_iff, Copy.induce, Copy.toEmbedding])
    (fun _ _ ↦ mem_univ _)
    (fun u hu ↦ by simp [Copy.ext_iff, Copy.induce])
    (fun u hu ↦ Copy.ext_iff.mpr (fun _ ↦ by rfl))

omit [Fintype α] in
/-- The number of copies of `B` in the induced subgraph of `A` by `s` is equal to the number of
copies of `B` in `A` with vertices in `s`. -/
theorem labelledCopyCount_induce_eq_card_subtype_copy (s : Finset α) :
    (A.induce s).labelledCopyCount B
      = card {f : Copy B A // univ.map f.toEmbedding ⊆ s} := by
  rw [labelledCopyCount_induce_eq_card_filter_copy,
    ← card_univ, ← subtype_univ, card_subtype]

omit [DecidableEq α] [Fintype (Copy B A)] in
/-- The number of copies of `B` in the induced subgraph of `A` by `s` is at most the number of
copies of `B` in `A`. -/
theorem labelledCopyCount_induce_le (s : Finset α) :
    (A.induce s).labelledCopyCount B ≤ A.labelledCopyCount B := by classical
  rw [labelledCopyCount_induce_eq_card_subtype_copy, labelledCopyCount_eq_card_copy]
  exact card_subtype_le (fun f : Copy B A ↦ univ.map f.toEmbedding ⊆ s)

end LabelledCopyCount

end SimpleGraph
