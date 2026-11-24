module

public import S3N9.Frame
public import S3N9.CellAlgebra

/-!
# The theorem for nine points: the Gram–Schmidt cell lemma

A labelled configuration `y` has the points `a, a', b, b'` at the positions `0, 1, 2, 3` and the ring points at
the positions `4, …, 8`. Its Gram–Schmidt frame (`def:gsframe`) is `fE y`, the direction of `a - a'`, and `fF y`,
the normalized part of the direction `fB y` of `b - b'` that is orthogonal to `fE y`. `hgt y l` is the height of
the point `l`.

`InCell C y` states the conditions (i) to (iii) of `def:gscell`. For a cell whose constants satisfy the
conditions (C1) to (C5) the cell lemma (`lma:gscell`) follows:

* `frameData`: the frame is defined and orthonormal, with the tilt `|s| ≤ σ̄`, and the identities of
  `lma:vrframeid`;
* `aPt_zero`, `aPt_one`, `bPt_two`, `bPt_three`, `rPt`: the bounds for the coordinates of the points
  (`GSCell.APt`, `GSCell.BPt`, `GSCell.RPt`);
* `cell_dir`: the direction of `b - b'` in the frame;
* `cell_gram`: `H² ≤ R R'` for any two points.

This is part of row A7 of `S3N9/README.md`.
-/

@[expose] public section

namespace S3N9

/-- The first vector of the Gram–Schmidt frame of a labelled configuration: the direction of `a - a'`. -/
noncomputable def fE (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := dirOf (y 0) (y 1)

/-- The direction of `b - b'`. -/
noncomputable def fB (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := dirOf (y 2) (y 3)

/-- The second vector of the Gram–Schmidt frame. -/
noncomputable def fF (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : EuclideanSpace ℝ (Fin 4) := frameF (fE y) (fB y)

/-- The height of a point: the squared length of its projection to the plane of the frame. -/
noncomputable def hgt (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) (l : Fin 9) : ℝ :=
  inner ℝ (y l) (fE y) ^ 2 + inner ℝ (y l) (fF y) ^ 2

/-- Half the length of `a - a'`. -/
noncomputable def lenA (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : ℝ := halfLen (y 0) (y 1)

/-- Half the length of `b - b'`. -/
noncomputable def lenB (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : ℝ := halfLen (y 2) (y 3)

/-- The tilt `σ₁₂ = ⟪e, e_B⟫`. -/
noncomputable def tiltS (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : ℝ := inner ℝ (fE y) (fB y)

noncomputable def tiltC (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : ℝ := √(1 - tiltS y ^ 2)

/-- A labelled configuration in a Gram–Schmidt cell: the conditions (i) to (iii) of `def:gscell`, without the
lower ends of the intervals. -/
structure InCell (C : GSCell) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  unit : ∀ l, ‖y l‖ = 1
  tA : inner ℝ (y 0) (y 1) ≤ -C.cA
  tB : inner ℝ (y 2) (y 3) ≤ -C.cB
  tilt : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → |inner ℝ (y i) (y j)| ≤ C.δ
  sep : ∀ i l : Fin 9, i.val < 4 → 4 ≤ l.val → inner ℝ (y i) (y l) ≤ C.T

/-- The frame of a labelled configuration in a cell: it is orthonormal, and the points of the two pairs have the
coordinates of `lma:vrframeid`. -/
structure FrameData (C : GSCell) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  tA1 : inner ℝ (y 0) (y 1) < 1
  tB1 : inner ℝ (y 2) (y 3) < 1
  eu : ‖fE y‖ = 1
  fu : ‖fF y‖ = 1
  ef : inner ℝ (fE y) (fF y) = 0
  rA0 : 0 < lenA y
  rA2 : 1 - C.ηA ≤ lenA y ^ 2
  rB0 : 0 < lenB y
  rB2 : 1 - C.ηB ≤ lenB y ^ 2
  s_le : |tiltS y| ≤ C.σ
  c0 : 0 < tiltC y
  sc : tiltS y ^ 2 + tiltC y ^ 2 = 1
  u0 : inner ℝ (y 0) (fE y) = lenA y
  u1 : inner ℝ (y 1) (fE y) = -lenA y
  v01 : inner ℝ (y 1) (fF y) = inner ℝ (y 0) (fF y)
  b2 : tiltS y * inner ℝ (y 2) (fE y) + tiltC y * inner ℝ (y 2) (fF y) = lenB y
  b3 : tiltS y * inner ℝ (y 3) (fE y) + tiltC y * inner ℝ (y 3) (fF y) = -lenB y
  eB : ∀ x : EuclideanSpace ℝ (Fin 4),
    inner ℝ x (fB y) = tiltS y * inner ℝ x (fE y) + tiltC y * inner ℝ x (fF y)
  subA : y 0 - y 1 = (2 * lenA y) • fE y
  subB : y 2 - y 3 = (2 * lenB y) • fB y
  eBf : fB y = tiltS y • fE y + tiltC y • fF y

section

variable {C : GSCell} (hC : C.Valid) (hP : C.Pos) {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : InCell C y)

include hC hP h

/-- **The frame of a configuration in a cell** (`lma:gscell`, first statement, and `lma:vrframeid`). -/
theorem frameData : FrameData C y := by
  have htA : inner ℝ (y 0) (y 1) < 1 := by linarith [h.tA, hP.cA0]
  have htB : inner ℝ (y 2) (y 3) < 1 := by
    have := h.tB
    rw [← hP.cAB] at this
    linarith [hP.cA0]
  have hrA2 : lenA y ^ 2 = (1 - inner ℝ (y 0) (y 1)) / 2 := halfLen_sq htA
  have hrA0 : 0 < lenA y := halfLen_pos htA
  have hrB2 : lenB y ^ 2 = (1 - inner ℝ (y 2) (y 3)) / 2 := halfLen_sq htB
  have hrB0 : 0 < lenB y := halfLen_pos htB
  have heu : ‖fE y‖ = 1 := norm_dir (h.unit 0) (h.unit 1) htA
  have hBu : ‖fB y‖ = 1 := norm_dir (h.unit 2) (h.unit 3) htB
  have gA : 1 - C.ηA ≤ lenA y ^ 2 := by
    rw [hrA2]
    unfold GSCell.ηA
    linarith [h.tA]
  have gB : 1 - C.ηB ≤ lenB y ^ 2 := by
    rw [hrB2]
    unfold GSCell.ηB
    linarith [h.tB]
  -- the tilt
  have hs : |tiltS y| ≤ C.σ := by
    have a1 : tiltS y = (2 * lenB y)⁻¹ * (inner ℝ (fE y) (y 2) - inner ℝ (fE y) (y 3)) := inner_dir (fE y)
    have a2 : inner ℝ (y 2) (fE y) = (2 * lenA y)⁻¹ * (inner ℝ (y 2) (y 0) - inner ℝ (y 2) (y 1)) :=
      inner_dir (y 2)
    have a3 : inner ℝ (y 3) (fE y) = (2 * lenA y)⁻¹ * (inner ℝ (y 3) (y 0) - inner ℝ (y 3) (y 1)) :=
      inner_dir (y 3)
    rw [real_inner_comm (y 2) (fE y), real_inner_comm (y 3) (fE y), a2, a3] at a1
    have t1 := abs_le.1 (h.tilt 0 2 (by decide) (by decide) (by decide))
    have t2 := abs_le.1 (h.tilt 1 2 (by decide) (by decide) (by decide))
    have t3 := abs_le.1 (h.tilt 0 3 (by decide) (by decide) (by decide))
    have t4 := abs_le.1 (h.tilt 1 3 (by decide) (by decide) (by decide))
    rw [real_inner_comm (y 2) (y 0)] at t1
    rw [real_inner_comm (y 2) (y 1)] at t2
    rw [real_inner_comm (y 3) (y 0)] at t3
    rw [real_inner_comm (y 3) (y 1)] at t4
    have e4 : tiltS y * (4 * (lenA y * lenB y))
        = inner ℝ (y 2) (y 0) - inner ℝ (y 2) (y 1) - (inner ℝ (y 3) (y 0) - inner ℝ (y 3) (y 1)) := by
      rw [a1]
      field_simp
      ring
    have hpos : 0 < lenA y * lenB y := mul_pos hrA0 hrB0
    have h5 : |tiltS y| * (lenA y * lenB y) ≤ C.δ := by
      have h6 : |tiltS y * (4 * (lenA y * lenB y))| ≤ 4 * C.δ := by
        rw [e4, abs_le]
        constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2]
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * (lenA y * lenB y))] at h6
      linarith
    have h7 : √((1 + C.cA) * (1 + C.cB)) ≤ 2 * (lenA y * lenB y) := by
      have h8 : (1 + C.cA) * (1 + C.cB) ≤ (2 * (lenA y * lenB y)) ^ 2 := by
        have e9 : (2 * (lenA y * lenB y)) ^ 2 = (2 * lenA y ^ 2) * (2 * lenB y ^ 2) := by ring
        rw [e9]
        have hcB : 0 ≤ 1 + C.cB := by
          rw [← hP.cAB]
          linarith [hP.cA0]
        refine mul_le_mul ?_ ?_ hcB (by positivity)
        · rw [hrA2]
          linarith [h.tA]
        · rw [hrB2]
          linarith [h.tB]
      have h9 := Real.sqrt_le_sqrt h8
      rwa [Real.sqrt_sq (by positivity)] at h9
    have h10 : C.δ ≤ C.σ * (lenA y * lenB y) := by
      have := mul_le_mul_of_nonneg_left h7 hP.σ0
      linarith [hC.c1a]
    exact le_of_mul_le_mul_right (le_trans h5 h10) hpos
  have hs1 : inner ℝ (fE y) (fB y) ^ 2 < 1 := lt_of_le_of_lt (sq_le_of_abs_le hs) (GSCell.σ_sq_lt hC hP)
  have hfu : ‖fF y‖ = 1 := frame_unit heu hBu hs1
  have hef : inner ℝ (fE y) (fF y) = 0 := frame_orth heu hs1
  have heB : ∀ x : EuclideanSpace ℝ (Fin 4),
      inner ℝ x (fB y) = tiltS y * inner ℝ x (fE y) + tiltC y * inner ℝ x (fF y) := fun x => inner_eB hs1 x
  have hsubA : y 0 - y 1 = (2 * lenA y) • fE y := sub_eq_smul_dir htA
  have hsubB : y 2 - y 3 = (2 * lenB y) • fB y := sub_eq_smul_dir htB
  have hu0 : inner ℝ (y 0) (fE y) = lenA y := inner_dir_left (h.unit 0) (h.unit 1) htA
  have hu1 : inner ℝ (y 1) (fE y) = -lenA y := inner_dir_right (h.unit 0) (h.unit 1) htA
  have hb2 : inner ℝ (y 2) (fB y) = lenB y := inner_dir_left (h.unit 2) (h.unit 3) htB
  have hb3 : inner ℝ (y 3) (fB y) = -lenB y := inner_dir_right (h.unit 2) (h.unit 3) htB
  refine ⟨htA, htB, heu, hfu, hef, hrA0, gA, hrB0, gB, hs, frame_c_pos hs1, ?_, hu0, hu1, ?_, ?_, ?_, heB, hsubA,
    hsubB, frame_eB hs1⟩
  · have := frame_c_sq (e := fE y) (eB := fB y) hs1
    show tiltS y ^ 2 + √(1 - tiltS y ^ 2) ^ 2 = 1
    unfold tiltS
    rw [this]
    ring
  · have e : inner ℝ (y 0 - y 1) (fF y) = 0 := by
      rw [hsubA, real_inner_smul_left, hef, mul_zero]
    rw [inner_sub_left] at e
    linarith
  · rw [← heB, hb2]
  · rw [← heB, hb3]

/-- The point `a`. -/
theorem aPt_zero : C.APt 1 (inner ℝ (y 0) (fE y)) (inner ℝ (y 0) (fF y)) := by
  have D := frameData hC hP h
  exact GSCell.aPt_of hC hP (by norm_num) (by rw [one_mul]; exact D.u0) D.rA2 D.rA0
    (bessel2 D.eu D.fu D.ef (h.unit 0))

/-- The point `a'`. -/
theorem aPt_one : C.APt (-1) (inner ℝ (y 1) (fE y)) (inner ℝ (y 1) (fF y)) := by
  have D := frameData hC hP h
  exact GSCell.aPt_of hC hP (by norm_num) (by rw [D.u1]; ring) D.rA2 D.rA0
    (bessel2 D.eu D.fu D.ef (h.unit 1))

/-- The point `b`. -/
theorem bPt_two : C.BPt 1 (inner ℝ (y 2) (fE y)) (inner ℝ (y 2) (fF y)) := by
  have D := frameData hC hP h
  exact GSCell.bPt_of hC hP (by norm_num) D.s_le D.c0 D.sc D.rB2 D.rB0 (by rw [one_mul]; exact D.b2)
    (bessel2 D.eu D.fu D.ef (h.unit 2))

/-- The point `b'`. -/
theorem bPt_three : C.BPt (-1) (inner ℝ (y 3) (fE y)) (inner ℝ (y 3) (fF y)) := by
  have D := frameData hC hP h
  exact GSCell.bPt_of hC hP (by norm_num) D.s_le D.c0 D.sc D.rB2 D.rB0 (by rw [D.b3]; ring)
    (bessel2 D.eu D.fu D.ef (h.unit 3))

/-- A ring point (`lma:gscell` (iii)). -/
theorem rPt (l : Fin 9) (hl : 4 ≤ l.val) : C.RPt (inner ℝ (y l) (fE y)) (inner ℝ (y l) (fF y)) := by
  have D := frameData hC hP h
  have hη1 : C.ηA ≤ 1 := by
    have := hC.c4c
    linarith [sq_nonneg C.T]
  have hu : |inner ℝ (y l) (fE y)| ≤ C.hcap C.cA := by
    rw [GSCell.hcap_eq hP]
    have hA := D.rA2
    unfold lenA at hA
    exact abs_inner_dir_le (h.unit 0) (h.unit 1) (h.unit l) D.tA1 (by linarith) hη1 hP.T0
      (by linarith [hC.c4c]) (h.sep 0 l (by decide) hl) (h.sep 1 l (by decide) hl)
  have hw : |inner ℝ (y l) (fB y)| ≤ C.hcap C.cA := by
    rw [GSCell.hcap_eq hP, ← GSCell.ηB_eq hP]
    have hB := D.rB2
    unfold lenB at hB
    exact abs_inner_dir_le (h.unit 2) (h.unit 3) (h.unit l) D.tB1 (by linarith)
      (by rw [GSCell.ηB_eq hP]; exact hη1) hP.T0 (by linarith [hC.c4d]) (h.sep 2 l (by decide) hl)
      (h.sep 3 l (by decide) hl)
  obtain ⟨h1, h2⟩ := GSCell.ring_alg hC hP D.s_le D.c0 D.sc (D.eB (y l)) hu hw
  exact ⟨h1, h2, by linarith [bessel2 D.eu D.fu D.ef (h.unit l)]⟩

/-- The direction of `b - b'` in the frame (`lma:gscell` (ii), last statement). -/
theorem cell_dir : (inner ℝ (y 2) (fE y) - inner ℝ (y 3) (fE y)) ^ 2
    ≤ C.κθ ^ 2 * (inner ℝ (y 2) (fF y) - inner ℝ (y 3) (fF y)) ^ 2 := by
  have D := frameData hC hP h
  have hff : inner ℝ (fF y) (fF y) = 1 := by rw [real_inner_self_eq_norm_sq, D.fu, one_pow]
  have hfe : inner ℝ (fF y) (fE y) = 0 := by rw [real_inner_comm, D.ef]
  have e1 : inner ℝ (y 2) (fE y) - inner ℝ (y 3) (fE y) = 2 * lenB y * tiltS y := by
    rw [← inner_sub_left, D.subB, real_inner_smul_left, real_inner_comm (fE y) (fB y)]
    rfl
  have e2 : inner ℝ (y 2) (fF y) - inner ℝ (y 3) (fF y) = 2 * lenB y * tiltC y := by
    rw [← inner_sub_left, D.subB, real_inner_smul_left, real_inner_comm (fF y) (fB y), D.eB, hfe, hff]
    ring
  rw [e1, e2]
  have hs2 : tiltS y ^ 2 ≤ C.σ ^ 2 := sq_le_of_abs_le D.s_le
  have h1 : tiltS y ^ 2 ≤ C.κθ ^ 2 * tiltC y ^ 2 := by
    have h2 : C.κθ ^ 2 * (1 - C.σ ^ 2) ≤ C.κθ ^ 2 * tiltC y ^ 2 :=
      mul_le_mul_of_nonneg_left (by linarith [D.sc]) (sq_nonneg _)
    linarith [hC.c3d]
  have h3 := mul_le_mul_of_nonneg_left h1 (sq_nonneg (2 * lenB y))
  calc (2 * lenB y * tiltS y) ^ 2 = (2 * lenB y) ^ 2 * tiltS y ^ 2 := by ring
    _ ≤ (2 * lenB y) ^ 2 * (C.κθ ^ 2 * tiltC y ^ 2) := h3
    _ = C.κθ ^ 2 * (2 * lenB y * tiltC y) ^ 2 := by ring

/-- The Gram determinant of the parts of two points orthogonal to the frame: `H² ≤ R R'`. -/
theorem cell_gram (i j : Fin 9) :
    (inner ℝ (y i) (y j) - inner ℝ (y i) (fE y) * inner ℝ (y j) (fE y)
        - inner ℝ (y i) (fF y) * inner ℝ (y j) (fF y)) ^ 2
      ≤ (1 - inner ℝ (y i) (fE y) ^ 2 - inner ℝ (y i) (fF y) ^ 2)
        * (1 - inner ℝ (y j) (fE y) ^ 2 - inner ℝ (y j) (fF y) ^ 2) := by
  have D := frameData hC hP h
  exact zeta_cs D.eu D.fu D.ef (h.unit i) (h.unit j)

end

/-- info: 'S3N9.rPt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rPt

/-- info: 'S3N9.bPt_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bPt_three

end S3N9
