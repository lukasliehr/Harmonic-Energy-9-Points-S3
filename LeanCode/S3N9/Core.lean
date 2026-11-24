module

public import S3N9.Leaves

/-!
# The theorem for nine points: the core of the cell L3-k2

`core_cover` (`prop:core`): a labelled configuration in the core has a relabelling in one of the two selected-edge
claims `Q2±in`, in one of the eleven leaves with a virtual-root certificate (`leavesVR`), or in the inner piece
`Leaf.I`. The proof follows the source: the largest height `M` of the ring points and a top point; for
`M ≤ 3 / 100` the tilt decides between `I`, `Q2±in` and `QW0`; for `M ≥ 3 / 100` the band of `M` and the position
of the top point give `WXj` or, after a relabelling of the ring that moves the top point to the first point of
`C`, `WYj`.

`l3k2_energy` (`prop:L3k2`): for a chain in the cell L3-k2 the energy is at least `35 / 2`, and if it is at most
`35 / 2`, a relabelling lies in the inner piece and has the contacts. The hypotheses are the statements that the
certificates provide (`Excl claimsRing`, `ExclSel claimsSel`, `ExclLeaves leavesVR`, `InnerOK`).

This is row A8 of `S3N9/README.md`; with `InnerOK` it contains row A9.
-/

@[expose] public section

namespace S3N9

/-- The heights after a relabelling that fixes the positions of the pairs `A` and `B`. -/
theorem hgt_comp {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (σ : Equiv.Perm (Fin 9)) (h0 : σ 0 = 0) (h1 : σ 1 = 1)
    (h2 : σ 2 = 2) (h3 : σ 3 = 3) (l : Fin 9) : hgt (y ∘ σ) l = hgt y (σ l) := by
  have e1 : fE (y ∘ σ) = fE y := by
    unfold fE
    simp only [Function.comp_apply, h0, h1]
  have e2 : fB (y ∘ σ) = fB y := by
    unfold fB
    simp only [Function.comp_apply, h2, h3]
  have e3 : fF (y ∘ σ) = fF y := by
    unfold fF
    rw [e1, e2]
  unfold hgt
  rw [e1, e3]
  rfl

/-- A relabelling of the ring that respects the pairs and moves a point of `C ∪ D` to the first point of `C`
(`lma:L3k2relabel`). -/
theorem exists_ringPerm : ∀ l : Fin 9, 4 ≤ l.val → l.val < 8 →
    ∃ σ : Equiv.Perm (Fin 9), Respects σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = l := by
  intro l h4 h8
  obtain ⟨l, hl⟩ := l
  simp only at h4 h8
  interval_cases l
  · exact (show ∃ σ : Equiv.Perm (Fin 9), Respects σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 4 from
      ⟨1, by decide +kernel⟩)
  · exact (show ∃ σ : Equiv.Perm (Fin 9), Respects σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 5 from
      ⟨Equiv.swap 4 5, by decide +kernel⟩)
  · exact (show ∃ σ : Equiv.Perm (Fin 9), Respects σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 6 from
      ⟨Equiv.swap 4 6 * Equiv.swap 5 7, by decide +kernel⟩)
  · exact (show ∃ σ : Equiv.Perm (Fin 9), Respects σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 3 = 3 ∧ σ 4 = 7 from
      ⟨Equiv.swap 4 7 * Equiv.swap 5 6, by decide +kernel⟩)

/-- A top point: a ring point of the largest height. -/
theorem exists_top (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) :
    ∃ l : Fin 9, 4 ≤ l.val ∧ ∀ m : Fin 9, 4 ≤ m.val → hgt y m ≤ hgt y l := by
  have hne : (Finset.univ.filter fun m : Fin 9 => 4 ≤ m.val).Nonempty :=
    ⟨8, Finset.mem_filter.2 ⟨Finset.mem_univ _, by decide⟩⟩
  obtain ⟨l, hl, hmax⟩ := Finset.exists_max_image _ (hgt y) hne
  exact ⟨l, (Finset.mem_filter.1 hl).2, fun m hm => hmax m (Finset.mem_filter.2 ⟨Finset.mem_univ _, hm⟩)⟩

/-- The bands cover the heights from `3 / 100` on (`lma:designation`). -/
theorem band_cover {M : ℝ} (h0 : 3 / 100 ≤ M) (h1 : M ≤ 1) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 5 ∧ ((Leaf.band j).1 : ℝ) ≤ M ∧ M ≤ ((Leaf.band j).2 : ℝ) := by
  have e1 : Leaf.band 1 = (3 / 100, 6 / 100) := rfl
  have e2 : Leaf.band 2 = (6 / 100, 9 / 100) := rfl
  have e3 : Leaf.band 3 = (9 / 100, 135 / 1000) := rfl
  have e4 : Leaf.band 4 = (135 / 1000, 1 / 5) := rfl
  have e5 : Leaf.band 5 = (3 / 20, 1) := rfl
  by_cases a1 : M ≤ 6 / 100
  · refine ⟨1, le_rfl, by norm_num, ?_, ?_⟩ <;> rw [e1] <;> push_cast <;> linarith
  by_cases a2 : M ≤ 9 / 100
  · refine ⟨2, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [e2] <;> push_cast <;> linarith
  by_cases a3 : M ≤ 135 / 1000
  · refine ⟨3, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [e3] <;> push_cast <;> linarith
  by_cases a4 : M ≤ 1 / 5
  · refine ⟨4, by norm_num, by norm_num, ?_, ?_⟩ <;> rw [e4] <;> push_cast <;> linarith
  · refine ⟨5, by norm_num, le_rfl, ?_, ?_⟩ <;> rw [e5] <;> push_cast <;> linarith

theorem mem_WX {j : ℕ} (h1 : 1 ≤ j) (h5 : j ≤ 5) : Leaf.WX j ∈ leavesVR := by
  interval_cases j <;> simp [leavesVR]

theorem mem_WY {j : ℕ} (h1 : 1 ≤ j) (h5 : j ≤ 5) : Leaf.WY j ∈ leavesVR := by
  interval_cases j <;> simp [leavesVR]

theorem δ_wide {L : Leaf} (h : L.wide = true) : (L.cellQ.δ : ℝ) = 3 / 10 := by
  unfold Leaf.cellQ
  rw [if_pos h]
  norm_num [cellQ30]

theorem δ_narrow {L : Leaf} (h : L.wide = false) : (L.cellQ.δ : ℝ) = 1 / 10 := by
  unfold Leaf.cellQ
  rw [if_neg (by rw [h]; decide)]
  norm_num [cellQ10]

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Core y)

include h

/-- A configuration of the core lies in the cells with the tilt bound `3 / 10`. -/
theorem core_inCell : InCell cellQ30.toCell y where
  unit := h.aux.unit
  tA := by
    show inner ℝ (y 0) (y 1) ≤ -(99 / 100 : ℝ)
    have := h.aux.near 0 1 (by decide) (by decide) (by decide)
    linarith
  tB := by
    show inner ℝ (y 2) (y 3) ≤ -(99 / 100 : ℝ)
    have := h.aux.near 2 3 (by decide) (by decide) (by decide)
    linarith
  tilt := fun i j hi hj2 hj4 => by
    have := h.tilt i j hi hj2 hj4
    show |inner ℝ (y i) (y j)| ≤ ((cellQ30.δ : ℚ) : ℝ)
    norm_num [cellQ30]
    linarith
  sep := fun i l hi hl => by
    show inner ℝ (y i) (y l) ≤ (1089 / 2000 : ℝ)
    exact le_of_lt (h.aux.sep i l (fun e => by rw [e] at hi; omega))

theorem hgt_le_one (l : Fin 9) : hgt y l ≤ 1 := by
  have D := frameData (by rw [cellQ30_eq]; exact cell30_valid) (by rw [cellQ30_eq]; exact cell30_pos)
    (core_inCell h)
  exact bessel2 D.eu D.fu D.ef (h.aux.unit l)

/-- **The cover of the core** (`prop:core`). -/
theorem core_cover : ∃ σ : Equiv.Perm (Fin 9),
    (∃ c ∈ claimsSel, InSC c (y ∘ σ)) ∨ (∃ L ∈ leavesVR, InLeaf L (y ∘ σ)) ∨ InLeaf Leaf.I (y ∘ σ) := by
  obtain ⟨lt, hlt4, hmax⟩ := exists_top y
  have hA0 := mval_zero_near h.aux
  have hB0 := mval_one_near h.aux
  have e01 : inner ℝ (y 0) (y 1) = mval y 0 := mval_eq rfl rfl
  have hh0 : ∀ l : Fin 9, 0 ≤ hgt y l := fun l => add_nonneg (sq_nonneg _) (sq_nonneg _)
  by_cases hM : hgt y lt ≤ 3 / 100
  · by_cases ht : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → |inner ℝ (y i) (y j)| ≤ 1 / 10
    · -- the inner piece
      refine ⟨1, Or.inr (Or.inr ?_)⟩
      rw [Equiv.Perm.coe_one, Function.comp_id]
      refine ⟨h.aux, fun i j hi hj2 hj4 => ?_, fun hs => ?_, fun l hl => ?_, ?_⟩
      · rw [δ_narrow rfl]
        exact ht i j hi hj2 hj4
      · exact absurd hs (by decide)
      · show hgt y l ≤ ((3 / 100 : ℚ) : ℝ)
        push_cast
        exact le_trans (hmax l hl) hM
      · show ((0 : ℚ) : ℝ) ≤ hgt y 8
        push_cast
        exact hh0 8
    · push Not at ht
      obtain ⟨i, j, hi, hj2, hj4, hij⟩ := ht
      by_cases hin : mval y 0 ≤ -(997 : ℝ) / 1000
      · -- both pairs are inner: a selected edge
        have lA : ((Cell.m1 : ℤ) : ℝ) / 2000 ≤ mval y 0 := by
          rw [m1_eq]
          exact neg_one_le_mval h.aux.unit (by norm_num)
        have lB : ((Cell.m1 : ℤ) : ℝ) / 2000 ≤ mval y 1 := by
          rw [m1_eq]
          exact neg_one_le_mval h.aux.unit (by norm_num)
        obtain ⟨σ, hσ⟩ := sel_of_tilt h.aux (d := 200)
          (ivl (a := Cell.m1) (b := Cell.cin) lA (by rw [cin_eq]; exact hin))
          (ivl (a := Cell.m1) (b := Cell.cin) lB (by rw [cin_eq]; linarith [h.bent])) hi hj2 hj4
          (by push_cast; linarith)
        rcases hσ with hσ | hσ
        · exact ⟨σ, Or.inl ⟨Cell.q2p, by decide, hσ⟩⟩
        · exact ⟨σ, Or.inl ⟨Cell.q2m, by decide, hσ⟩⟩
      · -- the leaf QW0
        rw [not_le] at hin
        refine ⟨1, Or.inr (Or.inl ⟨Leaf.QW0, by simp [leavesVR], ?_⟩)⟩
        rw [Equiv.Perm.coe_one, Function.comp_id]
        refine ⟨h.aux, fun i j hi hj2 hj4 => ?_, fun _ => ?_, fun l hl => ?_, ?_⟩
        · rw [δ_wide rfl]
          exact h.tilt i j hi hj2 hj4
        · rw [e01]
          linarith
        · show hgt y l ≤ ((3 / 100 : ℚ) : ℝ)
          push_cast
          exact le_trans (hmax l hl) hM
        · show ((0 : ℚ) : ℝ) ≤ hgt y 8
          push_cast
          exact hh0 8
  · rw [not_le] at hM
    obtain ⟨j, hj1, hj5, hb1, hb2⟩ := band_cover (le_of_lt hM) (hgt_le_one h lt)
    by_cases h8 : lt.val = 8
    · -- the top point is `x`
      have hlt : lt = 8 := Fin.ext h8
      refine ⟨1, Or.inr (Or.inl ⟨Leaf.WX j, mem_WX hj1 hj5, ?_⟩)⟩
      rw [Equiv.Perm.coe_one, Function.comp_id]
      refine ⟨h.aux, fun i j hi hj2 hj4 => ?_, fun hs => ?_, fun l hl => ?_, ?_⟩
      · rw [δ_wide rfl]
        exact h.tilt i j hi hj2 hj4
      · exact absurd hs Bool.false_ne_true
      · show hgt y l ≤ ((Leaf.band j).2 : ℝ)
        exact le_trans (hmax l hl) hb2
      · show ((Leaf.band j).1 : ℝ) ≤ hgt y 8
        rw [← hlt]
        exact hb1
    · -- the top point lies in `C ∪ D`: it becomes the first point of `C`
      obtain ⟨σ, hσ, s0, s1, s2, s3, s4⟩ := exists_ringPerm lt hlt4 (by have := lt.isLt; omega)
      have hfix : ∀ i : Fin 9, i.val < 4 → σ i = i := by
        intro i hi
        obtain ⟨i, hi9⟩ := i
        simp only at hi
        interval_cases i
        · exact s0
        · exact s1
        · exact s2
        · exact s3
      have hring : ∀ l : Fin 9, 4 ≤ l.val → 4 ≤ (σ l).val := by
        intro l hl
        have := hσ.2 l
        unfold pr at this
        omega
      refine ⟨σ, Or.inr (Or.inl ⟨Leaf.WY j, mem_WY hj1 hj5, ?_⟩)⟩
      refine ⟨h.aux.comp hσ, fun i j hi hj2 hj4 => ?_, fun hs => ?_, fun l hl => ?_, ?_⟩
      · rw [δ_wide rfl]
        show |inner ℝ (y (σ i)) (y (σ j))| ≤ 3 / 10
        rw [hfix i (by omega), hfix j hj4]
        exact h.tilt i j hi hj2 hj4
      · exact absurd hs Bool.false_ne_true
      · show hgt (y ∘ σ) l ≤ ((Leaf.band j).2 : ℝ)
        rw [hgt_comp σ s0 s1 s2 s3]
        exact le_trans (hmax (σ l) (hring l hl)) hb2
      · show ((Leaf.band j).1 : ℝ) ≤ hgt (y ∘ σ) 4
        rw [hgt_comp σ s0 s1 s2 s3, s4]
        exact hb1

end

/-- **The cell L3-k2** (`prop:L3k2`, with `thm:inner`). Given the statements of the certificates, the energy of a
chain in the cell L3-k2 is at least `35 / 2`; if it is at most `35 / 2`, a relabelling of the chain lies in the
inner piece and has the contacts. -/
theorem l3k2_energy (hR : Excl claimsRing) (hS : ExclSel claimsSel) (hV : ExclLeaves leavesVR) (hI : InnerOK)
    {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)
    (h0 : mval y 0 ≤ -(99 : ℝ) / 100) (h1 : mval y 1 ≤ -(99 : ℝ) / 100) (hf2 : -(9 : ℝ) / 10 < mval y 2) :
    (35 : ℝ) / 2 ≤ energyE y
      ∧ (energyE y ≤ 35 / 2 → ∃ ρ : Equiv.Perm (Fin 9), InLeaf Leaf.I (y ∘ ρ) ∧ Contacts (y ∘ ρ)) := by
  rcases l3k2_outer_energy hR hS hu hs hc h0 h1 hf2 with hgt' | ⟨σ, hcore⟩
  · exact ⟨le_of_lt hgt', fun hle => absurd hle (not_le.2 hgt')⟩
  · obtain ⟨τ, hτ⟩ := core_cover hcore
    have e : energyE ((y ∘ ⇑σ) ∘ ⇑τ) = energyE y := by
      rw [energyE_comp_perm, energyE_comp_perm]
    have e2 : (y ∘ ⇑σ) ∘ ⇑τ = y ∘ ⇑(σ * τ) := by
      rw [Equiv.Perm.coe_mul]
      rfl
    rcases hτ with ⟨c, hc', hin⟩ | ⟨L, hL, hin⟩ | hin
    · have := hS c hc' _ hin
      rw [e] at this
      exact ⟨le_of_lt this, fun hle => absurd hle (not_le.2 this)⟩
    · have := hV L hL _ hin
      rw [e] at this
      exact ⟨le_of_lt this, fun hle => absurd hle (not_le.2 this)⟩
    · obtain ⟨a, b⟩ := hI _ hin
      rw [e] at a b
      refine ⟨a, fun hle => ⟨σ * τ, ?_, ?_⟩⟩
      · rw [← e2]
        exact hin
      · rw [← e2]
        exact b hle

/-- info: 'S3N9.l3k2_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms l3k2_energy

end S3N9
