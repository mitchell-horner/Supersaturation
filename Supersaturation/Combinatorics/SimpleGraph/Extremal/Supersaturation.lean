import Mathlib
import Supersaturation.Combinatorics.SimpleGraph.Copy
import Supersaturation.Combinatorics.SimpleGraph.Extremal.TuranDensity
import Supersaturation.Combinatorics.SimpleGraph.Finite
import Supersaturation.Data.Finset.Powerset
import Supersaturation.Data.Nat.Choose.Basic

open Asymptotics Filter Finset Fintype Function Real Topology

namespace SimpleGraph

variable {W : Type*} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]

namespace Supersaturation

variable {n : ℕ} {ε : ℝ}

open Classical in
/-- `overFin` is the finset of simple graphs having an edge density at least `turanDensity H + ε`.

This is an auxiliary definition for the **supersaturation theorem**. -/
noncomputable abbrev overFin (n : ℕ) (H : SimpleGraph W) (ε : ℝ) : Finset (SimpleGraph (Fin n)) :=
  { F : SimpleGraph (Fin n) | ∃ _ : DecidableRel F.Adj,
    #F.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 }

omit [Fintype W] [DecidableRel H.Adj] in
lemma top_mem_overFin_univ (hn : 2 ≤ n) (h : H.turanDensity + ε ≤ 1) :
    ⊤ ∈ overFin n H ε := by
  classical refine (mem_filter_univ ⊤).mpr ⟨inferInstance, ?_⟩
  rwa [card_edgeFinset_top_eq_card_choose_two, ge_iff_le, Fintype.card_fin n,
    mul_le_iff_le_one_left (mod_cast Nat.choose_pos hn)]

omit [Fintype W] [DecidableRel H.Adj] in
theorem overFin_nonempty (hn : 2 ≤ n) (h : H.turanDensity + ε ≤ 1) : (overFin n H ε).Nonempty :=
  ⟨⊤, top_mem_overFin_univ hn h⟩

/-- `overFin.minLabelledCopyCount` is the minimum number of copies of `H` in any simple graph
in `overFin`.

This is an auxiliary definition for the **supersaturation theorem**. -/
noncomputable abbrev overFin.minLabelledCopyCount
    (n : ℕ) (H : SimpleGraph W) (ε : ℝ) :=
  WithTop.untopD 0 <| (overFin n H ε).inf (labelledCopyCount · H)

omit [DecidableRel H.Adj] in
theorem overFin.minLabelledCopyCount_eq_inf' (hn : 2 ≤ n) (h : H.turanDensity + ε ≤ 1) :
    overFin.minLabelledCopyCount n H ε
      = (overFin n H ε).inf' (overFin_nonempty hn h) (labelledCopyCount · H) := by
  rw [WithTop.untopD_eq_iff, coe_inf']
  refine Or.inl rfl

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

open Classical in
/-- `overPowersetCard` is the finset of `n`-sized finsets of vertices whose induced subgraphs
`G.induce s` have an edge density at least `turanDensity H + ε`.

This is an auxiliary definition for the **supersaturation theorem**. -/
noncomputable abbrev overPowersetCard
    (G : SimpleGraph (Fin n)) (k : ℕ) (H : SimpleGraph W) (ε : ℝ) : Finset (Finset (Fin n)) :=
  { s ∈ univ.powersetCard k | #(G.induce s.toSet).edgeFinset ≥ (turanDensity H + ε) * k.choose 2 }

omit [Fintype W] [DecidableRel H.Adj] in
/-- This is an auxiliary definition for the **supersaturation theorem**. -/
theorem card_overPowersetCard_ge {k : ℕ} (hk : 2 ≤ k) (hn : k ≤ n)
    (hcard_edges : #G.edgeFinset ≥ (H.turanDensity + ε) * n.choose 2)
    (hπ : (H.turanDensity + ε / 2) < 1) :
    (ε / 2 / (1 - (turanDensity H + ε / 2))) * n.choose k
      ≤ #(overPowersetCard G k H (ε / 2)) := by
  -- double count the `k`-sized sets with induced subgraphs that have sufficent edges
  let S := overPowersetCard G k H (ε / 2)
  have hS_subset : S ⊆ univ.powersetCard k := filter_subset _ _
  have hS : #G.edgeFinset * (n - 2).choose (k - 2) ≤ #S * k.choose 2
      + (n.choose k - #S) * (H.turanDensity + ε / 2) * k.choose 2 := by classical
    -- double count `(s, e)` where `s` is an `k`-sized subset containing the vertices of `e`
    let T := (univ.powersetCard k ×ˢ G.edgeFinset).filter fun (s, e) ↦ e.toFinset ⊆ s
    trans (#T : ℝ)
    · have he {e : G.edgeFinset} := hk.trans_eq' (card_toFinset_mem_edgeFinset e)
      simp_rw [T, card_filter, sum_product_right, ← card_filter, ← sum_attach G.edgeFinset,
        card_filter_powersetCard_superset (subset_univ _) he, card_univ,
        card_toFinset_mem_edgeFinset, sum_const, smul_eq_mul, card_attach, Nat.cast_mul,
        Fintype.card_fin, le_rfl]
    · simp_rw [T, card_filter, sum_product, ← card_filter, filter_edgeFinset_toFinset_subset]
      let inst (s : Finset (Fin n)) : Fintype ↑↑s := Subtype.fintype (Membership.mem s)
      conv =>
        enter [1, 1, 2, s, 1]
        rw [← @toFinset_coe _ s (inst s), ← map_edgeFinset_induce]
      simp_rw [card_map, ← sum_inter_add_sum_diff (univ.powersetCard k) S,
        inter_eq_right.mpr hS_subset, Nat.cast_add]
      apply add_le_add
      · rw [← Nat.cast_mul, Nat.cast_le, ← smul_eq_mul, ← sum_const]
        apply sum_le_sum (fun s hs ↦ ?_)
        trans (card s.toSet).choose 2
        · convert card_edgeFinset_le_card_choose_two
        · apply hS_subset at hs
          rw [mem_powersetCard_univ] at hs
          simp_rw [coe_sort_coe, card_coe, hs, le_rfl]
      · conv =>
          enter [2, 1, 1, 1]
          rw [← Fintype.card_fin n]
        rw [mul_assoc, ← card_univ, ← card_powersetCard,
          ← Nat.cast_sub (card_le_card hS_subset), ← card_sdiff_of_subset hS_subset,
          ← smul_eq_mul, Nat.cast_smul_eq_nsmul, ← sum_const, Nat.cast_sum]
        refine sum_le_sum (fun s hs ↦ ?_)
        obtain ⟨hs, nhs⟩ := mem_sdiff.mp hs
        contrapose! nhs with hcard_edges
        exact mem_filter.mpr ⟨hs, by convert hcard_edges.le.ge⟩
  -- solve for `#S` using the bound on the number of edges of `G`
  rw [← div_le_div_iff_of_pos_right (mod_cast Nat.choose_pos hn : (0 : ℝ) < n.choose k),
    ← div_le_div_iff_of_pos_right (mod_cast Nat.choose_pos hk : (0 : ℝ) < k.choose 2), div_div,
    mul_div_assoc, ← Nat.cast_mul, Nat.choose_mul hn hk, Nat.cast_mul, div_mul_cancel_right₀ <|
    mod_cast Nat.choose_ne_zero (Nat.sub_le_sub_right hn 2), ← div_eq_mul_inv] at hS
  rw [ge_iff_le, ← le_div_iff₀ <| mod_cast Nat.choose_pos (hk.trans hn)] at hcard_edges
  apply hcard_edges.trans at hS
  rwa [div_div, add_div, mul_div_assoc, div_mul_cancel_right₀ (mod_cast Nat.choose_ne_zero hk),
    ← div_eq_mul_inv, mul_assoc, mul_comm _ (_ * _), mul_sub, sub_div, mul_assoc,
    mul_comm (k.choose 2 : ℝ) _, mul_div_cancel_right₀ _ <|
    mul_ne_zero (mod_cast Nat.choose_ne_zero hn) (mod_cast Nat.choose_ne_zero hk),
    ← mul_rotate, mul_div_assoc, div_mul_cancel_right₀ (mod_cast Nat.choose_ne_zero hk),
    ← div_eq_mul_inv, mul_comm (#S : ℝ) _, ← add_sub_assoc, ← sub_add_eq_add_sub, mul_div_assoc,
    ← one_sub_mul, ← sub_le_iff_le_add, add_tsub_add_eq_tsub_left, sub_half,
    ← div_le_iff₀' (sub_pos_of_lt hπ), le_div_iff₀ (mod_cast Nat.choose_pos hn)] at hS

/-- This is an auxiliary definition for the **supersaturation theorem**. -/
theorem card_overPowersetCard_le
  {k : ℕ} (hk : 2 ≤ k) (hcard : card W ≤ k) (h : H.turanDensity + ε ≤ 1) :
  (overFin.minLabelledCopyCount k H ε) * #(overPowersetCard G k H ε)
    ≤ G.labelledCopyCount H * (n - card W).choose (k - card W) := by
  -- double count `(s, f)` where `s` is an `k`-sized subset containing the image of `f`
  classical let T := (univ.powersetCard k ×ˢ univ).filter
              fun (s, (f : Copy H G)) ↦ univ.map f.toEmbedding ⊆ s
  trans #T
  · simp_rw [T, card_filter, sum_product, mul_sum]
    refine sum_le_sum (fun s hs ↦ ?_)
    classical rw [← card_filter, mul_ite, mul_one, mul_zero,
      ← labelledCopyCount_induce_eq_card_filter_copy s]
    split_ifs with hcard_edges
    · have : Nonempty (s.toSet ≃ Fin k) := by
        simp_rw [← card_eq, coe_sort_coe, card_coe, Fintype.card_fin, mem_powersetCard_univ.mp hs]
      let f : s.toSet ≃ Fin k := Classical.arbitrary (s.toSet ≃ Fin k)
      have hf : (G.induce s.toSet).map f.toEmbedding ∈ overFin k H ε := by
        simp_rw [mem_filter_univ]
        refine ⟨inferInstance, ?_⟩
        simp_rw [(G.induce s.toSet).card_edgeFinset_map f.toEmbedding]
        convert hcard_edges
      simp_rw [overFin.minLabelledCopyCount_eq_inf' hk h, inf'_le_iff]
      exact ⟨(G.induce s.toSet).map f.toEmbedding, hf,
        by rw [← labelledCopyCount_congr_left (Iso.map f _)]⟩
    · exact Nat.zero_le <| (G.induce s.toSet).labelledCopyCount H
  · have hf {f : Copy H G} : #(univ.map f.toEmbedding) ≤ k := by
      rwa [← card_univ, ← card_map f.toEmbedding] at hcard
    classical simp_rw [T, card_filter, sum_product_right, ← card_filter,
      card_filter_powersetCard_superset (subset_univ _) hf, card_map, card_univ,
      Fintype.card_fin, sum_const, smul_eq_mul, card_univ, labelledCopyCount_eq_card_copy, le_rfl]

end Supersaturation

/-- If `G` has sufficently many vertices `n` and at least `(turanDensity H + ε) * n.choose 2`
many edges, then `G` contains at least `δ * n ^ v(H)` copies of `H`.

This is the **supersaturation theorem** for simple graphs. -/
theorem labelledCopyCount_ge_of_card_edgeFinset {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ δ > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
        #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 →
          G.labelledCopyCount H ≥ δ * n ^ card W := by
  rcases lt_or_ge 1 (turanDensity H + ε) with hπH_ε | hπH_ε
  · refine ⟨1, zero_lt_one, 2, fun n hn {G} _ hcard_edges ↦ ?_⟩
    absurd hcard_edges
    push_neg
    apply lt_of_lt_of_le' (lt_mul_left (mod_cast Nat.choose_pos hn) hπH_ε)
    conv_rhs =>
      rw [← Fintype.card_fin n]
    exact_mod_cast card_edgeFinset_le_card_choose_two
    -- (lt_mul_left (mod_cast Nat.choose_pos hn) hπH_ε)
  · have hπH_halfε : turanDensity H + ε / 2 < 1 := by
      apply hπH_ε.trans_lt'
      rw [add_lt_add_iff_left, half_lt_self_iff]
      exact hε_pos
    -- find `t` such that every `F ∈ overFin` contains `H`
    have ⟨t', ht'⟩ := isContained_of_card_edgeFinset H (half_pos hε_pos)
    let t := max (max 2 t') (card W)
    -- bounds on `t`
    have ht_2 : 2 ≤ t := le_max_of_le_left (le_max_left 2 t')
    have ht_t' : t' ≤ t := le_max_of_le_left (le_max_right 2 t')
    have ht_cardW : card W ≤ t := le_max_right (max 2 t') (card W)
    -- find the minimum number of copies of `H` in any `F`
    let c :=  Supersaturation.overFin.minLabelledCopyCount t H (ε / 2)
    -- show there is at least 1 copy of `H` in any `F`
    have hc_pos : 0 < c := by
      simp_rw [c, Supersaturation.overFin.minLabelledCopyCount_eq_inf' ht_2 hπH_halfε.le,
          lt_inf'_iff, mem_filter_univ, forall_exists_index, labelledCopyCount_pos]
      intro F _ hF
      exact ht' t ht_t' hF
    -- eventually `m * n ^ card W` is less than `n.choose (card W)` for some fixed `m`
    have ⟨m, hm_pos, N, hpow_le_choose⟩ :
        ∃ m > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, m * n ^ card W ≤ n.choose (card W) := by
      simpa [isBigO_iff''] using (isTheta_choose (card W)).symm.isBigO
    -- pick `δ'` such that `δ := δ' * m`
    let δ' := c * (ε / 2 / (1 - (turanDensity H + ε / 2))) / t.choose (card W)
    have hδ'_pos : 0 < δ' := by
      refine div_pos (mul_pos (mod_cast hc_pos) ?_) ?_
      · apply div_pos (half_pos hε_pos)
        rwa [← sub_pos] at hπH_halfε
      · exact mod_cast Nat.choose_pos ht_cardW
    refine ⟨δ' * m, mul_pos hδ'_pos hm_pos, max t N, fun n hn G _ hcard_edges ↦ ?_⟩
    have ht_n : t ≤ n := (le_max_left t N).trans hn
    -- there are at least `δ' * n.choose (card W)` copies of `H` in `G`
    have h : δ' * n.choose (card W) ≤ G.labelledCopyCount H := by
      have hchoose_mul : (n.choose (card W) : ℝ)
          = n.choose t / (n - card W).choose (t - card W) * t.choose (card W) := by
        rw [div_mul_eq_mul_div, eq_div_iff_mul_eq (mod_cast Nat.choose_sub_ne_zero ht_n)]
        exact_mod_cast (Nat.choose_mul ht_n ht_cardW).symm
      rw [hchoose_mul, mul_rotate', mul_div_cancel₀ _ (mod_cast Nat.choose_ne_zero ht_cardW),
        div_mul_eq_mul_div, mul_comm, div_le_iff₀ (mod_cast Nat.choose_sub_pos ht_n)]
      trans c * #(Supersaturation.overPowersetCard G t H (ε / 2))
      · rw [mul_assoc, mul_le_mul_iff_right₀ (mod_cast hc_pos)]
        exact Supersaturation.card_overPowersetCard_ge ht_2 ht_n hcard_edges hπH_halfε
      · norm_cast
        exact Supersaturation.card_overPowersetCard_le ht_2 ht_cardW hπH_halfε.le
    rw [mul_assoc]
    refine h.trans' (mul_le_mul_of_nonneg_left ?_ hδ'_pos.le)
    exact hpow_le_choose n <| hn.trans' (le_max_right t N)

end SimpleGraph
