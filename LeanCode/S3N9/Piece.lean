module

public import CAP.VR.Sphere
public import S3N9.CellLemma

/-!
# The theorem for nine points: from a Gram–Schmidt cell to the piece of a virtual-root certificate

The theorem of a virtual-root certificate (`CAP.VR.energy_gt`) has the hypothesis `CAP.VR.InPieceS P heads y e f`:
the inequalities of the cell lemma with the constants `P` of the certificate, the intervals of the record types,
and the guards. `inPieceS_of_cell` derives it for the Gram–Schmidt frame of a labelled configuration in a cell
`C` whose constants are dominated by those of the certificate (`Dominates P heads C`).

This is part of row A7 of `S3N9/README.md`.
-/

@[expose] public section

namespace S3N9

open CAP.VR
open CAP.Wsos (nth)

/-- **The constants of a certificate dominate those of a cell**: every localizer of the certificate is
nonnegative on the cell. -/
structure Dominates (P : Par) (heads : List RecH) (C : GSCell) : Prop where
  aP : (P.cA.aPd : ℝ) * (2 ^ P.mAP * C.εAP) ≤ P.cA.aPn
  aQ : (P.cA.aQ2d : ℝ) * (2 ^ P.mAQ * C.εAQ) ^ 2 ≤ P.cA.aQ2n
  aη : (P.cA.etad : ℝ) * C.ηA ≤ P.cA.etan
  aT : (P.cA.td : ℝ) * C.κA ^ 2 ≤ P.cA.tn
  ag1 : (P.cA.g1 : ℝ) = P.cA.g2
  ag0 : (P.cA.g2 : ℝ) * C.ηA ≤ P.cA.g0
  bP : (P.cB.aPd : ℝ) * (2 ^ P.mBP * C.εBP) ≤ P.cB.aPn
  bQ : (P.cB.aQ2d : ℝ) * (2 ^ P.mBQ * C.εBQ) ^ 2 ≤ P.cB.aQ2n
  bη : (P.cB.etad : ℝ) * C.ηB ≤ P.cB.etan
  bT : (P.cB.td : ℝ) * C.κB ^ 2 ≤ P.cB.tn
  bg1 : (7 : ℝ) * P.cB.g1 ≤ 12 * P.cB.g2
  bg0 : (P.cB.g2 : ℝ) * (12 / 5 * C.σ ^ 2 + 12 / 7 * C.ηB) ≤ P.cB.g0
  dir : (P.dird : ℝ) * C.κθ ^ 2 ≤ P.dirn
  eR : (P.eR2d : ℝ) * C.εR ^ 2 ≤ P.eR2n
  sAB : ∀ i j : ℕ, i < 2 → 2 ≤ j → j < 4 →
    ((hdOf P heads i j).aS2d : ℝ) * (2 ^ (hdOf P heads i j).mS * C.σAB) ^ 2 ≤ (hdOf P heads i j).aS2n
  sAR : ∀ i j : ℕ, i < 2 → 4 ≤ j → j < 9 →
    ((hdOf P heads i j).aS2d : ℝ) * (2 ^ (hdOf P heads i j).mS * C.σAR) ^ 2 ≤ (hdOf P heads i j).aS2n
  sBR : ∀ i j : ℕ, 2 ≤ i → i < 4 → 4 ≤ j → j < 9 →
    ((hdOf P heads i j).aS2d : ℝ) * (2 ^ (hdOf P heads i j).mS * C.σBR) ^ 2 ≤ (hdOf P heads i j).aS2n

theorem scale_sq {a n d σ : ℝ} {m : ℕ} (ha : 0 ≤ a) (hd : d ^ 2 ≤ σ ^ 2) (hD : a * (2 ^ m * σ) ^ 2 ≤ n) :
    a * (2 ^ m * d) ^ 2 ≤ n := by
  have h1 : (2 ^ m * d) ^ 2 ≤ (2 ^ m * σ) ^ 2 := by
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_left hd (by positivity)
  have h2 := mul_le_mul_of_nonneg_left h1 ha
  linarith

variable {P : Par} {heads : List RecH} {C : GSCell}

/-- The localizers of a point of the pair `A`. -/
theorem pairPt_A (D : Dominates P heads C) {ε u v : ℝ} (h : C.APt ε u v) :
    PairPt P.cA P.mAP P.mAQ (ε * u) v (1 - u ^ 2 - v ^ 2) where
  major := by
    have h1 : (2 : ℝ) ^ P.mAP * (1 - ε * u) ≤ 2 ^ P.mAP * C.εAP := mul_le_mul_of_nonneg_left h.p1 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg P.cA.aPd : (0 : ℝ) ≤ P.cA.aPd)
    linarith [D.aP]
  minor := scale_sq (Nat.cast_nonneg _) h.q D.aQ
  eta := by
    have h2 := mul_le_mul_of_nonneg_left h.r1 (Nat.cast_nonneg P.cA.etad : (0 : ℝ) ≤ P.cA.etad)
    linarith [D.aη]
  cone := by
    have h1 := mul_le_mul_of_nonneg_left h.cone (Nat.cast_nonneg P.cA.td : (0 : ℝ) ≤ P.cA.td)
    have h2 := mul_le_mul_of_nonneg_right D.aT (sq_nonneg (ε * u))
    linarith
  gs := by
    rw [D.ag1]
    have h2 := mul_le_mul_of_nonneg_left h.gs (Nat.cast_nonneg P.cA.g2 : (0 : ℝ) ≤ P.cA.g2)
    linarith [D.ag0]

/-- The localizers of a point of the pair `B`. -/
theorem pairPt_B (D : Dominates P heads C) {ε u v : ℝ} (h : C.BPt ε u v) :
    PairPt P.cB P.mBP P.mBQ (ε * v) u (1 - u ^ 2 - v ^ 2) where
  major := by
    have h1 : (2 : ℝ) ^ P.mBP * (1 - ε * v) ≤ 2 ^ P.mBP * C.εBP := mul_le_mul_of_nonneg_left h.p1 (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg P.cB.aPd : (0 : ℝ) ≤ P.cB.aPd)
    linarith [D.bP]
  minor := scale_sq (Nat.cast_nonneg _) h.q D.bQ
  eta := by
    have h2 := mul_le_mul_of_nonneg_left h.r1 (Nat.cast_nonneg P.cB.etad : (0 : ℝ) ≤ P.cB.etad)
    linarith [D.bη]
  cone := by
    have h1 := mul_le_mul_of_nonneg_left h.cone (Nat.cast_nonneg P.cB.td : (0 : ℝ) ≤ P.cB.td)
    have h2 := mul_le_mul_of_nonneg_right D.bT (sq_nonneg (ε * v))
    linarith
  gs := by
    have h1 := mul_le_mul_of_nonneg_left h.gs (Nat.cast_nonneg P.cB.g2 : (0 : ℝ) ≤ P.cB.g2)
    have h2 := mul_le_mul_of_nonneg_right D.bg1 h.r0
    linarith [D.bg0]

theorem pt_nat (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) {l : ℕ} (hl : l < 9) : pt y l = y ⟨l, hl⟩ := by
  unfold pt
  rw [dif_pos hl]

theorem eps_zero : eps 0 = 1 := by
  unfold eps
  norm_num

theorem eps_one : eps 1 = -1 := by
  unfold eps
  norm_num

theorem eps_two : eps 2 = 1 := by
  unfold eps
  norm_num

theorem eps_three : eps 3 = -1 := by
  unfold eps
  norm_num

section

variable (hC : C.Valid) (hP : C.Pos) {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : InCell C y)

include hC hP h

theorem aPt_nat : ∀ i : ℕ, i < 2 → C.APt (eps i) (inner ℝ (pt y i) (fE y)) (inner ℝ (pt y i) (fF y)) := by
  intro i hi
  interval_cases i
  · rw [eps_zero, show pt y 0 = y 0 from pt_coe y 0]
    exact aPt_zero hC hP h
  · rw [eps_one, show pt y 1 = y 1 from pt_coe y 1]
    exact aPt_one hC hP h

theorem bPt_nat : ∀ j : ℕ, 2 ≤ j → j < 4 → C.BPt (eps j) (inner ℝ (pt y j) (fE y)) (inner ℝ (pt y j) (fF y)) := by
  intro j h2 h4
  interval_cases j
  · rw [eps_two, show pt y 2 = y 2 from pt_coe y 2]
    exact bPt_two hC hP h
  · rw [eps_three, show pt y 3 = y 3 from pt_coe y 3]
    exact bPt_three hC hP h

theorem rPt_nat : ∀ l : ℕ, 4 ≤ l → l < 9 → C.RPt (inner ℝ (pt y l) (fE y)) (inner ℝ (pt y l) (fF y)) := by
  intro l h4 h9
  rw [pt_nat y h9]
  exact rPt hC hP h ⟨l, h9⟩ h4

theorem gram_nat : ∀ i j : ℕ, i < 9 → j < 9 →
    (inner ℝ (pt y i) (pt y j) - inner ℝ (pt y i) (fE y) * inner ℝ (pt y j) (fE y)
        - inner ℝ (pt y i) (fF y) * inner ℝ (pt y j) (fF y)) ^ 2
      ≤ (1 - inner ℝ (pt y i) (fE y) ^ 2 - inner ℝ (pt y i) (fF y) ^ 2)
        * (1 - inner ℝ (pt y j) (fE y) ^ 2 - inner ℝ (pt y j) (fF y) ^ 2) := by
  intro i j hi hj
  rw [pt_nat y hi, pt_nat y hj]
  exact cell_gram hC hP h ⟨i, hi⟩ ⟨j, hj⟩

/-- **A labelled configuration in a cell lies in the piece of a certificate** whose constants dominate those of
the cell, if the inner products lie in the intervals of the record types and the heights of the ring points
satisfy the guards of the certificate. The frame is the Gram–Schmidt frame of the configuration. -/
theorem inPieceS_of_cell (D : Dominates P heads C)
    (hiv : ∀ i j : ℕ, i < j → j < 9 →
      ((hdOf P heads i j).lop : ℝ) - (hdOf P heads i j).lon ≤ (hdOf P heads i j).lod * inner ℝ (pt y i) (pt y j)
        ∧ (hdOf P heads i j).hid * inner ℝ (pt y i) (pt y j) ≤ ((hdOf P heads i j).hip : ℝ) - (hdOf P heads i j).hin)
    (hG : ∀ l : Fin 9, 4 ≤ l.val → (P.Gd : ℝ) * hgt y l ≤ P.Gn)
    (hlow : ∀ l : Fin 9, 4 ≤ l.val →
      (nth P.lowN (nth P.dcls l.val - 2) : ℝ) ≤ nth P.lowD (nth P.dcls l.val - 2) * hgt y l) :
    InPieceS P heads y (fE y) (fF y) := by
  have F := frameData hC hP h
  refine ⟨h.unit, F.eu, F.fu, F.ef, ?_, ?_, ?_, ?_, ?_, ?_, hiv, ?_⟩
  · rw [F.u0]
    exact F.subA
  · refine ⟨2 * lenB y * tiltS y, 2 * lenB y * tiltC y, ?_⟩
    rw [F.subB]
    conv_lhs => rw [F.eBf]
    rw [smul_add, smul_smul, smul_smul]
  · exact fun l hl => pairPt_A D (aPt_nat hC hP h l hl)
  · exact fun l h2 h4 => pairPt_B D (bPt_nat hC hP h l h2 h4)
  · rw [show pt y 2 = y 2 from pt_coe y 2, show pt y 3 = y 3 from pt_coe y 3]
    have h1 := cell_dir hC hP h
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg P.dird : (0 : ℝ) ≤ P.dird)
    have h3 := mul_le_mul_of_nonneg_right D.dir
      (sq_nonneg (inner ℝ (y 2) (fF y) - inner ℝ (y 3) (fF y)))
    linarith
  · intro l h4 h9
    have r := rPt_nat hC hP h l h4 h9
    have g1 := hG ⟨l, h9⟩ h4
    have g2 := hlow ⟨l, h9⟩ h4
    rw [pt_nat y h9] at r ⊢
    refine ⟨?_, ?_, g1, g2⟩
    · have := mul_le_mul_of_nonneg_left r.u2 (Nat.cast_nonneg P.eR2d : (0 : ℝ) ≤ P.eR2d)
      linarith [D.eR]
    · have := mul_le_mul_of_nonneg_left r.v2 (Nat.cast_nonneg P.eR2d : (0 : ℝ) ≤ P.eR2d)
      linarith [D.eR]
  · intro i j hij hj9 hi4 hj2 hor
    have hH := gram_nat hC hP h i j (by omega) hj9
    unfold devS
    by_cases hi2 : i < 2
    · rw [if_pos hi2]
      by_cases hj4 : j < 4
      · rw [if_pos hj4]
        exact scale_sq (Nat.cast_nonneg _)
          (GSCell.devAB hC hP (aPt_nat hC hP h i hi2) (bPt_nat hC hP h j hj2 hj4) hH) (D.sAB i j hi2 hj2 hj4)
      · rw [if_neg hj4]
        exact scale_sq (Nat.cast_nonneg _)
          (GSCell.devAR hC hP (aPt_nat hC hP h i hi2) (rPt_nat hC hP h j (by omega) hj9) hH)
          (D.sAR i j hi2 (by omega) hj9)
    · rw [if_neg hi2]
      have hj4 : 4 ≤ j := by omega
      exact scale_sq (Nat.cast_nonneg _)
        (GSCell.devBR hC hP (bPt_nat hC hP h i (by omega) hi4) (rPt_nat hC hP h j hj4 hj9) hH)
        (D.sBR i j (by omega) hi4 hj4 hj9)

end

/-- info: 'S3N9.inPieceS_of_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inPieceS_of_cell

end S3N9
