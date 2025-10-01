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
protected def map' (f : α ≃ β) : Copy (A.map f.toEmbedding) A :=
  ⟨⟨f.symm, fun h ↦ by simpa [Equiv.apply_eq_iff_eq_symm_apply] using h⟩, f.symm.injective⟩

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
    (A.induce s.toSet).labelledCopyCount B
      = #{f : Copy B A | univ.map f.toEmbedding ⊆ s} := by
  classical rw [labelledCopyCount_eq_card_copy]
  apply card_bij' (fun f _ ↦ (Copy.induce A s).comp f)
      (fun f hf ↦ ⟨⟨fun w ↦ ⟨f w, ?_⟩, f.toHom.map_adj⟩, ?_⟩)
      (fun u hu ↦ ?_) (fun _ _ ↦ by simp) (fun u hu ↦ ?_) (fun u hu ↦ ?_)
  · rw [mem_filter_univ] at hf
    exact hf (mem_map_of_mem _ (mem_univ w))
  · simpa [Injective] using f.injective
  · simp [subset_iff, Copy.induce, Embedding.subtype,
      Embedding.induce, Copy.toEmbedding]
  · simp [Copy.ext_iff, Copy.induce, Embedding.subtype]
  · simp [Copy.ext_iff, Copy.induce, Embedding.subtype]

omit [Fintype α] in
/-- The number of copies of `B` in the induced subgraph of `A` by `s` is equal to the number of
copies of `B` in `A` with vertices in `s`. -/
theorem labelledCopyCount_induce_eq_card_subtype_copy (s : Finset α) :
    (A.induce s.toSet).labelledCopyCount B
      = card {f : Copy B A // univ.map f.toEmbedding ⊆ s} := by
  rw [labelledCopyCount_induce_eq_card_filter_copy,
    ← card_univ, ← subtype_univ, card_subtype]

/-- The number of copies of `B` in the induced subgraph of `A` by `s` is at most the number of
copies of `B` in `A`. -/
theorem labelledCopyCount_induce_le (s : Finset α) :
    (A.induce s.toSet).labelledCopyCount B ≤ A.labelledCopyCount B := by
  rw [labelledCopyCount_induce_eq_card_subtype_copy, labelledCopyCount_eq_card_copy]
  exact card_subtype_le (fun f : Copy B A ↦ univ.map f.toEmbedding ⊆ s)

end LabelledCopyCount

end SimpleGraph
