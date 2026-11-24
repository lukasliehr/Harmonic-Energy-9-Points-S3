module

public import S3N9.Piece
public import S3N9.L3k2

/-!
# The theorem for nine points: the leaves of the core and the pieces of their certificates

A leaf of the core of the cell L3-k2 (`def:coreclaims`) is given by data of the paper (`Leaf`): the tilt bound
(`1 / 10` or `3 / 10`, which selects the constants of the Gram–Schmidt cell), the lower end of the interval of the
pair `A`, the typing of the ring, the cap of the heights and a lower guard for the height of one ring point.
`InLeaf L y` states that a labelled configuration lies in the leaf: it lies in the claim *aux2*, and satisfies the
tilt bound, the cap and the guard, with the heights in its Gram–Schmidt frame.

* `inner_ge_cap` (`lma:cap`): the cap bound, from which the intervals `[L*, T]` between a point of a near pair and
  a ring point follow.
* `CellQ`, `cellQ10`, `cellQ30`: the constants of the two sets of cells as rational numbers.
* `fitsLeaf P heads L`: the constants of a certificate dominate those of the cell of the leaf, its record
  intervals contain the intervals of the leaf, and its guards are those of the leaf. These are comparisons of
  rational numbers, which the kernel decides for the data of a certificate.
* `inPieceS_of_leaf`: a labelled configuration in a leaf lies in the piece of a certificate that fits.
* `ExclLeaves l`, `InnerOK`: what the library needs from the eleven virtual-root certificates and from the sharp
  certificate; `exclLeaf_of_cert`, `innerOK_of_cert` derive them from the theorems of the certificates.

This completes row A7 of `S3N9/README.md`.
-/

@[expose] public section

namespace S3N9

open CAP.VR
open CAP.Wsos (nth)

/-! ## The cap bound -/

/-- The cap bound in the plane. -/
theorem cap2d {A b c T : ℝ} (hc0 : 0 < c) (hcA : c ≤ A) (hA1 : A ≤ 1) (hb : b ≤ T) (hb1 : -1 ≤ b) (hT0 : 0 ≤ T)
    (hTc : T ≤ c) :
    A * b + √(1 - A ^ 2) * √(1 - b ^ 2) ≤ c * T + √(1 - c ^ 2) * √(1 - T ^ 2) := by
  have hA0 : 0 < A := lt_of_lt_of_le hc0 hcA
  have hc1 : c ≤ 1 := le_trans hcA hA1
  have hA2 : A ^ 2 ≤ 1 := by nlinarith
  have hb2 : b ^ 2 ≤ 1 := by nlinarith
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hcA2 : c ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (le_of_lt hc0) hcA 2
  obtain ⟨Sa, hSa⟩ : ∃ s : ℝ, s = √(1 - A ^ 2) := ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ s : ℝ, s = √(1 - b ^ 2) := ⟨_, rfl⟩
  obtain ⟨Sc, hSc⟩ : ∃ s : ℝ, s = √(1 - c ^ 2) := ⟨_, rfl⟩
  have hSac : Sa ≤ Sc := by
    rw [hSa, hSc]
    exact Real.sqrt_le_sqrt (by linarith)
  rw [← hSa, ← hSb, ← hSc]
  have hSa0 : 0 ≤ Sa := by
    rw [hSa]
    exact Real.sqrt_nonneg _
  have hSb0 : 0 ≤ Sb := by
    rw [hSb]
    exact Real.sqrt_nonneg _
  have hSc0 : 0 ≤ Sc := le_trans hSa0 hSac
  have hSa2 : Sa ^ 2 = 1 - A ^ 2 := by
    rw [hSa]
    exact Real.sq_sqrt (by linarith)
  have hSb2 : Sb ^ 2 = 1 - b ^ 2 := by
    rw [hSb]
    exact Real.sq_sqrt (by linarith)
  have hSc2 : Sc ^ 2 = 1 - c ^ 2 := by
    rw [hSc]
    exact Real.sq_sqrt (by linarith)
  have hL0 : 0 ≤ c * T + Sc * √(1 - T ^ 2) :=
    add_nonneg (mul_nonneg (le_of_lt hc0) hT0) (mul_nonneg hSc0 (Real.sqrt_nonneg _))
  by_cases hU : 0 ≤ A * b + Sa * Sb
  · have hW : 0 ≤ A * Sb - Sa * b := by
      by_cases hb0 : b ≤ 0
      · have h1 := mul_nonneg (le_of_lt hA0) hSb0
        have h2 := mul_nonneg hSa0 (neg_nonneg.2 hb0)
        linarith
      · rw [not_le] at hb0
        have hbA : b ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (le_of_lt hb0) (by linarith) 2
        have h1 : (Sa * b) ^ 2 ≤ (A * Sb) ^ 2 := by
          rw [mul_pow, mul_pow, hSa2, hSb2]
          linarith
        have h2 := sq_le_sq.1 h1
        rw [abs_of_nonneg (mul_nonneg hSa0 (le_of_lt hb0)), abs_of_nonneg (mul_nonneg (le_of_lt hA0) hSb0)] at h2
        linarith
    have hTc2 : T ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hT0 hTc 2
    refine cap_core (r := A) (m := Sa) (U := A * b + Sa * Sb) (W := A * Sb - Sa * b) (T := T) (r₀ := c) (m₀ := Sc)
      hSa0 hSac hA0 (by rw [hSa2]; ring) (le_of_lt hc0) (by rw [hSc2]; ring) hT0 (by rw [hSc2]; linarith) hU hW
      ?_ ?_
    · have e : (A * b + Sa * Sb) ^ 2 + (A * Sb - Sa * b) ^ 2 = (A ^ 2 + Sa ^ 2) * (b ^ 2 + Sb ^ 2) := by ring
      rw [e, hSa2, hSb2]
      ring
    · have e : A * (A * b + Sa * Sb) - Sa * (A * Sb - Sa * b) = (A ^ 2 + Sa ^ 2) * b := by ring
      rw [e, hSa2]
      linarith
  · rw [not_le] at hU
    linarith

/-- **The cap bound** (`lma:cap`): if `⟪p, q⟫ ≤ -c` and `⟪q, y⟫ ≤ T` for unit vectors and `0 ≤ T ≤ c`, then
`⟪p, y⟫ ≥ -(c T + √(1 - c²) √(1 - T²))`. -/
theorem inner_ge_cap {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {p q y : V} (hp : ‖p‖ = 1)
    (hq : ‖q‖ = 1) (hy : ‖y‖ = 1) {c T : ℝ} (hc0 : 0 < c) (hT0 : 0 ≤ T) (hTc : T ≤ c)
    (hpq : inner ℝ p q ≤ -c) (hqy : inner ℝ q y ≤ T) :
    -(c * T + √(1 - c ^ 2) * √(1 - T ^ 2)) ≤ inner ℝ p y := by
  have ha1 : |inner ℝ p q| ≤ 1 := by
    have := abs_real_inner_le_norm p q
    rwa [hp, hq, mul_one] at this
  have hb1 : |inner ℝ q y| ≤ 1 := by
    have := abs_real_inner_le_norm q y
    rwa [hq, hy, mul_one] at this
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = inner ℝ p q := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = inner ℝ q y := ⟨_, rfl⟩
  rw [← ha] at ha1 hpq
  rw [← hb] at hb1 hqy
  have hqq : inner ℝ q q = 1 := by rw [real_inner_self_eq_norm_sq, hq, one_pow]
  have h1 : inner ℝ (p - a • q) (y - b • q) = inner ℝ p y - a * b := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_left, hqq, ← ha, ← hb]
    ring
  have h2 : ‖p - a • q‖ ^ 2 = 1 - a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_left, hqq, real_inner_self_eq_norm_sq, hp,
      real_inner_comm p q, ← ha]
    ring
  have h3 : ‖y - b • q‖ ^ 2 = 1 - b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_left, hqq, real_inner_self_eq_norm_sq, hy,
      real_inner_comm q y, ← hb]
    ring
  have h4 := abs_real_inner_le_norm (p - a • q) (y - b • q)
  have h5 : ‖p - a • q‖ = √(1 - a ^ 2) := by rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  have h6 : ‖y - b • q‖ = √(1 - b ^ 2) := by rw [← h3, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, h5, h6] at h4
  have h7 := (abs_le.1 h4).1
  have h8 := cap2d (A := -a) (b := b) hc0 (by linarith) (by linarith [(abs_le.1 ha1).1]) hqy (abs_le.1 hb1).1 hT0
    hTc
  rw [neg_sq] at h8
  linarith

/-! ## The constants of the cells as rational numbers -/

/-- The constants of a Gram–Schmidt cell with the caps `99 / 100` and the separation bound `1089 / 2000`. -/
structure CellQ where
  δ : ℚ
  σ : ℚ
  εAP : ℚ
  εAQ : ℚ
  κA : ℚ
  εBP : ℚ
  εBQ : ℚ
  κB : ℚ
  κθ : ℚ
  εR : ℚ
  σAB : ℚ
  σAR : ℚ
  σBR : ℚ

noncomputable def CellQ.toCell (Q : CellQ) : GSCell :=
  ⟨99 / 100, 99 / 100, Q.δ, 1089 / 2000, Q.σ, Q.εAP, Q.εAQ, Q.κA, Q.εBP, Q.εBQ, Q.κB, Q.κθ, Q.εR, Q.σAB, Q.σAR,
    Q.σBR⟩

/-- The constants of the cells with the tilt bound `1 / 10`. -/
def cellQ10 : CellQ :=
  ⟨1 / 10, 2512563 / 25000000, 313 / 125000, 70711 / 1000000, 70889 / 1000000, 14661 / 1000000, 42651 / 250000,
    86571 / 500000, 50507 / 500000, 833 / 1250, 13 / 2000, 1197 / 10000, 243 / 1250⟩

/-- The constants of the cells with the tilt bound `3 / 10`. -/
def cellQ30 : CellQ :=
  ⟨3 / 10, 15075377 / 50000000, 313 / 125000, 70711 / 1000000, 70889 / 1000000, 70243 / 1000000,
    368173 / 1000000, 395989 / 1000000, 4941 / 15625, 514 / 625, 109 / 10000, 1311 / 10000, 4317 / 10000⟩

theorem cellQ10_eq : cellQ10.toCell = cell10 := by
  simp only [CellQ.toCell, cellQ10, cell10]
  norm_num

theorem cellQ30_eq : cellQ30.toCell = cell30 := by
  simp only [CellQ.toCell, cellQ30, cell30]
  norm_num

theorem toCell_ηA (Q : CellQ) : Q.toCell.ηA = 1 / 200 := by
  simp only [GSCell.ηA, CellQ.toCell]
  norm_num

theorem toCell_ηB (Q : CellQ) : Q.toCell.ηB = 1 / 200 := by
  simp only [GSCell.ηB, CellQ.toCell]
  norm_num

theorem cell10_pos : cell10.Pos :=
  ⟨by norm_num [cell10], by norm_num [cell10], rfl, by norm_num [cell10], by norm_num [cell10], by norm_num [cell10]⟩

theorem cell30_pos : cell30.Pos :=
  ⟨by norm_num [cell30], by norm_num [cell30], rfl, by norm_num [cell30], by norm_num [cell30], by norm_num [cell30]⟩

/-- **The constants of a certificate dominate those of a cell**, as comparisons of rational numbers. -/
def domFits (P : Par) (heads : List RecH) (Q : CellQ) : Prop :=
  (P.cA.aPd : ℚ) * (2 ^ P.mAP * Q.εAP) ≤ P.cA.aPn
    ∧ (P.cA.aQ2d : ℚ) * (2 ^ P.mAQ * Q.εAQ) ^ 2 ≤ P.cA.aQ2n
    ∧ (P.cA.etad : ℚ) * (1 / 200) ≤ P.cA.etan
    ∧ (P.cA.td : ℚ) * Q.κA ^ 2 ≤ P.cA.tn
    ∧ P.cA.g1 = P.cA.g2
    ∧ (P.cA.g2 : ℚ) * (1 / 200) ≤ P.cA.g0
    ∧ (P.cB.aPd : ℚ) * (2 ^ P.mBP * Q.εBP) ≤ P.cB.aPn
    ∧ (P.cB.aQ2d : ℚ) * (2 ^ P.mBQ * Q.εBQ) ^ 2 ≤ P.cB.aQ2n
    ∧ (P.cB.etad : ℚ) * (1 / 200) ≤ P.cB.etan
    ∧ (P.cB.td : ℚ) * Q.κB ^ 2 ≤ P.cB.tn
    ∧ 7 * P.cB.g1 ≤ 12 * P.cB.g2
    ∧ (P.cB.g2 : ℚ) * (12 / 5 * Q.σ ^ 2 + 12 / 7 * (1 / 200)) ≤ P.cB.g0
    ∧ (P.dird : ℚ) * Q.κθ ^ 2 ≤ P.dirn
    ∧ (P.eR2d : ℚ) * Q.εR ^ 2 ≤ P.eR2n
    ∧ (∀ j < 4, ∀ i < 2, 2 ≤ j →
      ((hdOf P heads i j).aS2d : ℚ) * (2 ^ (hdOf P heads i j).mS * Q.σAB) ^ 2 ≤ (hdOf P heads i j).aS2n)
    ∧ (∀ j < 9, ∀ i < 2, 4 ≤ j →
      ((hdOf P heads i j).aS2d : ℚ) * (2 ^ (hdOf P heads i j).mS * Q.σAR) ^ 2 ≤ (hdOf P heads i j).aS2n)
    ∧ (∀ j < 9, ∀ i < 4, 2 ≤ i → 4 ≤ j →
      ((hdOf P heads i j).aS2d : ℚ) * (2 ^ (hdOf P heads i j).mS * Q.σBR) ^ 2 ≤ (hdOf P heads i j).aS2n)

noncomputable instance (P : Par) (heads : List RecH) (Q : CellQ) : Decidable (domFits P heads Q) := by
  unfold domFits
  infer_instance

theorem dominates_of_fits {P : Par} {heads : List RecH} {Q : CellQ} (h : domFits P heads Q) :
    Dominates P heads Q.toCell := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := h
  have eA := toCell_ηA Q
  have eB := toCell_ηB Q
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [CellQ.toCell]
    exact_mod_cast h1
  · simp only [CellQ.toCell]
    exact_mod_cast h2
  · have := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at this
    rw [eA]
    linarith
  · simp only [CellQ.toCell]
    exact_mod_cast h4
  · exact_mod_cast h5
  · have := (Rat.cast_le (K := ℝ)).2 h6
    push_cast at this
    rw [eA]
    linarith
  · simp only [CellQ.toCell]
    exact_mod_cast h7
  · simp only [CellQ.toCell]
    exact_mod_cast h8
  · have := (Rat.cast_le (K := ℝ)).2 h9
    push_cast at this
    rw [eB]
    linarith
  · simp only [CellQ.toCell]
    exact_mod_cast h10
  · exact_mod_cast h11
  · have := (Rat.cast_le (K := ℝ)).2 h12
    push_cast at this
    rw [eB]
    simp only [CellQ.toCell]
    linarith
  · simp only [CellQ.toCell]
    exact_mod_cast h13
  · simp only [CellQ.toCell]
    exact_mod_cast h14
  · intro i j hi hj2 hj4
    have := h15 j hj4 i hi hj2
    simp only [CellQ.toCell]
    exact_mod_cast this
  · intro i j hi hj4 hj9
    have := h16 j hj9 i hi hj4
    simp only [CellQ.toCell]
    exact_mod_cast this
  · intro i j hi2 hi4 hj4 hj9
    have := h17 j hj9 i hi4 hi2 hj4
    simp only [CellQ.toCell]
    exact_mod_cast this

/-! ## The leaves of the core -/

/-- A leaf of the core (`def:coreclaims`), as data of the paper. -/
structure Leaf where
  /-- the tilt bound is `3 / 10` (the cells `C_Q`, `C_W`, `C_Y`); otherwise it is `1 / 10` (the cell `C_I`) -/
  wide : Bool
  /-- the pair `A` is in the shell: `t_A ≥ -997 / 1000` (the cell `C_Q`) -/
  shell : Bool
  /-- the pairs `C` and `D` have the interval `[-9 / 10, -3 / 4]` (the paired and the singleton typing) -/
  typed : Bool
  /-- the cap of the heights of the ring points (`1` if the leaf has none) -/
  cap : ℚ
  /-- the position of the ring point with the lower guard -/
  lowL : Fin 9
  /-- the lower guard (`0` if the leaf has none) -/
  low : ℚ
deriving DecidableEq, Repr

namespace Leaf

/-- The constants of the cell of a leaf. -/
def cellQ (L : Leaf) : CellQ := if L.wide then cellQ30 else cellQ10

/-- The interval of the inner product of the points at the positions `i < j` in a leaf. -/
def iv (L : Leaf) (i j : ℕ) : ℚ × ℚ :=
  if j < 2 then (if L.shell then -997 / 1000 else -1, -99 / 100)
  else if j < 4 then (if i < 2 then (-L.cellQ.δ, L.cellQ.δ) else (-1, -99 / 100))
  else if i < 4 then (-657377 / 1000000, 1089 / 2000)
  else if L.typed ∧ ((i = 4 ∧ j = 5) ∨ (i = 6 ∧ j = 7)) then (-9 / 10, -3 / 4)
  else (-9 / 10, 1089 / 2000)

/-- The bands of the heights: `s_{j-1}` and `s_j` for `j = 1, …, 4`, and `3 / 20`, `1` for `j = 5`. -/
def band (j : ℕ) : ℚ × ℚ :=
  if j = 1 then (3 / 100, 6 / 100) else if j = 2 then (6 / 100, 9 / 100) else if j = 3 then (9 / 100, 135 / 1000)
  else if j = 4 then (135 / 1000, 1 / 5) else (3 / 20, 1)

/-- The inner piece `I`. -/
def I : Leaf := ⟨false, false, false, 3 / 100, 8, 0⟩
/-- The leaf `QW0`. -/
def QW0 : Leaf := ⟨true, true, true, 3 / 100, 8, 0⟩
/-- The leaf `WXj`: the top point is `x`. -/
def WX (j : ℕ) : Leaf := ⟨true, false, true, (band j).2, 8, (band j).1⟩
/-- The leaf `WYj`: the top point is the first point of `C`. -/
def WY (j : ℕ) : Leaf := ⟨true, false, true, (band j).2, 4, (band j).1⟩

end Leaf

/-- The eleven leaves of the core with a virtual-root certificate with margin. -/
def leavesVR : List Leaf :=
  [Leaf.QW0, Leaf.WX 1, Leaf.WX 2, Leaf.WX 3, Leaf.WX 4, Leaf.WX 5, Leaf.WY 1, Leaf.WY 2, Leaf.WY 3, Leaf.WY 4,
    Leaf.WY 5]

/-- **A labelled configuration in a leaf of the core.** -/
structure InLeaf (L : Leaf) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  aux : Aux2 y
  tilt : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → |inner ℝ (y i) (y j)| ≤ (L.cellQ.δ : ℝ)
  shell : L.shell = true → -(997 : ℝ) / 1000 ≤ inner ℝ (y 0) (y 1)
  cap : ∀ l : Fin 9, 4 ≤ l.val → hgt y l ≤ (L.cap : ℝ)
  low : (L.low : ℝ) ≤ hgt y L.lowL

/-- **A certificate fits a leaf**: its constants dominate those of the cell, its record intervals contain the
intervals of the leaf, and its guards are implied by those of the leaf. -/
def fitsLeaf (P : Par) (heads : List RecH) (L : Leaf) : Prop :=
  domFits P heads L.cellQ
    ∧ (∀ j < 9, ∀ i < j,
      ((hdOf P heads i j).lop : ℚ) - (hdOf P heads i j).lon ≤ (hdOf P heads i j).lod * (L.iv i j).1
        ∧ (hdOf P heads i j).hid * (L.iv i j).2 ≤ ((hdOf P heads i j).hip : ℚ) - (hdOf P heads i j).hin)
    ∧ (P.Gd : ℚ) * L.cap ≤ P.Gn
    ∧ ∀ l < 9, 4 ≤ l →
      (nth P.lowN (nth P.dcls l - 2) : ℚ) ≤ nth P.lowD (nth P.dcls l - 2) * (if l = L.lowL.val then L.low else 0)

noncomputable instance (P : Par) (heads : List RecH) (L : Leaf) : Decidable (fitsLeaf P heads L) := by
  unfold fitsLeaf
  infer_instance

theorem Leaf.cell_valid (L : Leaf) : L.cellQ.toCell.Valid := by
  unfold Leaf.cellQ
  split_ifs
  · rw [cellQ30_eq]
    exact cell30_valid
  · rw [cellQ10_eq]
    exact cell10_valid

theorem Leaf.cell_pos (L : Leaf) : L.cellQ.toCell.Pos := by
  unfold Leaf.cellQ
  split_ifs
  · rw [cellQ30_eq]
    exact cell30_pos
  · rw [cellQ10_eq]
    exact cell10_pos

theorem partner_spec : ∀ i : Fin 9, i.val < 4 → ∃ i' : Fin 9, i ≠ i' ∧ pr i = pr i' ∧ pr i < 2 := by
  decide +kernel

section

variable {L : Leaf} {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : InLeaf L y)

include h

theorem inCell_of_leaf : InCell L.cellQ.toCell y where
  unit := h.aux.unit
  tA := by
    show inner ℝ (y 0) (y 1) ≤ -(99 / 100 : ℝ)
    have := h.aux.near 0 1 (by decide) (by decide) (by decide)
    linarith
  tB := by
    show inner ℝ (y 2) (y 3) ≤ -(99 / 100 : ℝ)
    have := h.aux.near 2 3 (by decide) (by decide) (by decide)
    linarith
  tilt := h.tilt
  sep := fun i l hi hl => by
    show inner ℝ (y i) (y l) ≤ (1089 / 2000 : ℝ)
    exact le_of_lt (h.aux.sep i l (fun e => by rw [e] at hi; omega))

/-- The inner product of a point of a near pair and a ring point is at least `L*`. -/
theorem lstar_le_inner (i l : Fin 9) (hi : i.val < 4) (hl : 4 ≤ l.val) :
    (-657377 / 1000000 : ℝ) ≤ inner ℝ (y i) (y l) := by
  obtain ⟨i', hne, hp, hp2⟩ := partner_spec i hi
  have h1 := h.aux.near i i' hne hp hp2
  have hi'l : i' ≠ l := fun e => by
    rw [e] at hp
    unfold pr at hp hp2
    omega
  have h2 := le_of_lt (h.aux.sep i' l hi'l)
  have h3 := inner_ge_cap (h.aux.unit i) (h.aux.unit i') (h.aux.unit l) (c := 99 / 100) (T := 1089 / 2000)
    (by norm_num) (by norm_num) (by norm_num) (by linarith) h2
  have h4 := lstar_le
  rw [Real.sqrt_mul (by norm_num)] at h4
  linarith

/-- The inner products of a configuration in a leaf lie in the intervals of the leaf. -/
theorem leaf_iv : ∀ i j : ℕ, i < j → j < 9 →
    ((L.iv i j).1 : ℝ) ≤ inner ℝ (CAP.VR.pt y i) (CAP.VR.pt y j)
      ∧ inner ℝ (CAP.VR.pt y i) (CAP.VR.pt y j) ≤ ((L.iv i j).2 : ℝ) := by
  intro i j hij hj
  have hi : i < 9 := by omega
  rw [pt_nat y hi, pt_nat y hj]
  have hne : (⟨i, hi⟩ : Fin 9) ≠ ⟨j, hj⟩ := fun e => by
    have := congrArg Fin.val e
    simp only at this
    omega
  have hu := abs_le.1 (by
    have := abs_real_inner_le_norm (y ⟨i, hi⟩) (y ⟨j, hj⟩)
    rwa [h.aux.unit, h.aux.unit, mul_one] at this : |inner ℝ (y ⟨i, hi⟩) (y ⟨j, hj⟩)| ≤ 1)
  have hsep := h.aux.sep ⟨i, hi⟩ ⟨j, hj⟩ hne
  unfold Leaf.iv
  by_cases c1 : j < 2
  · have hnear := h.aux.near ⟨i, hi⟩ ⟨j, hj⟩ hne (by unfold pr; simp only; omega) (by unfold pr; simp only; omega)
    rw [if_pos c1]
    have e0 : (⟨i, hi⟩ : Fin 9) = 0 := Fin.ext (by simp only; omega)
    have e1 : (⟨j, hj⟩ : Fin 9) = 1 := Fin.ext (by simp only; omega)
    constructor
    · by_cases hs : L.shell = true
      · rw [if_pos hs]
        have := h.shell hs
        rw [← e0, ← e1] at this
        push_cast
        linarith
      · rw [if_neg hs]
        push_cast
        linarith [hu.1]
    · push_cast
      linarith
  · rw [if_neg c1]
    by_cases c2 : j < 4
    · rw [if_pos c2]
      by_cases c3 : i < 2
      · rw [if_pos c3]
        have := abs_le.1 (h.tilt ⟨i, hi⟩ ⟨j, hj⟩ c3 (by simp only; omega) c2)
        push_cast
        exact this
      · rw [if_neg c3]
        have hnear := h.aux.near ⟨i, hi⟩ ⟨j, hj⟩ hne (by unfold pr; simp only; omega)
          (by unfold pr; simp only; omega)
        push_cast
        constructor <;> linarith [hu.1]
    · rw [if_neg c2]
      by_cases c3 : i < 4
      · rw [if_pos c3]
        have := lstar_le_inner h ⟨i, hi⟩ ⟨j, hj⟩ c3 (by simp only; omega)
        push_cast
        constructor <;> linarith
      · rw [if_neg c3]
        have hfar := h.aux.far ⟨i, hi⟩ ⟨j, hj⟩ hne (Or.inr (by unfold pr; simp only; omega))
        by_cases c4 : L.typed ∧ ((i = 4 ∧ j = 5) ∨ (i = 6 ∧ j = 7))
        · rw [if_pos c4]
          have hmid := h.aux.mid ⟨i, hi⟩ ⟨j, hj⟩ hne (by unfold pr; simp only; omega)
            (by unfold pr; simp only; omega)
          push_cast
          constructor <;> linarith
        · rw [if_neg c4]
          push_cast
          constructor <;> linarith

/-- **A labelled configuration in a leaf lies in the piece of a certificate that fits the leaf.** -/
theorem inPieceS_of_leaf {P : Par} {heads : List RecH} (hf : fitsLeaf P heads L) :
    InPieceS P heads y (fE y) (fF y) := by
  obtain ⟨f1, f2, f3, f4⟩ := hf
  refine inPieceS_of_cell L.cell_valid L.cell_pos (inCell_of_leaf h) (dominates_of_fits f1) ?_ ?_ ?_
  · intro i j hij hj
    obtain ⟨a1, a2⟩ := f2 j hj i hij
    obtain ⟨b1, b2⟩ := leaf_iv h i j hij hj
    have a1' : ((hdOf P heads i j).lop : ℝ) - (hdOf P heads i j).lon
        ≤ (hdOf P heads i j).lod * ((L.iv i j).1 : ℝ) := by exact_mod_cast a1
    have a2' : ((hdOf P heads i j).hid : ℝ) * ((L.iv i j).2 : ℝ)
        ≤ ((hdOf P heads i j).hip : ℝ) - (hdOf P heads i j).hin := by exact_mod_cast a2
    have c1 := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg (hdOf P heads i j).lod : (0 : ℝ) ≤ _)
    have c2 := mul_le_mul_of_nonneg_left b2 (Nat.cast_nonneg (hdOf P heads i j).hid : (0 : ℝ) ≤ _)
    exact ⟨le_trans a1' c1, le_trans c2 a2'⟩
  · intro l hl
    have f3' : (P.Gd : ℝ) * (L.cap : ℝ) ≤ P.Gn := by exact_mod_cast f3
    have := mul_le_mul_of_nonneg_left (h.cap l hl) (Nat.cast_nonneg P.Gd : (0 : ℝ) ≤ _)
    linarith
  · intro l hl
    have g := f4 l.val l.isLt hl
    have hh0 : 0 ≤ hgt y l := add_nonneg (sq_nonneg _) (sq_nonneg _)
    by_cases e : l.val = L.lowL.val
    · rw [if_pos e] at g
      have g' : (nth P.lowN (nth P.dcls l.val - 2) : ℝ) ≤ nth P.lowD (nth P.dcls l.val - 2) * (L.low : ℝ) := by
        exact_mod_cast g
      have hl' : l = L.lowL := Fin.ext e
      have := mul_le_mul_of_nonneg_left (by rw [hl']; exact h.low : (L.low : ℝ) ≤ hgt y l)
        (Nat.cast_nonneg (nth P.lowD (nth P.dcls l.val - 2)) : (0 : ℝ) ≤ _)
      linarith
    · rw [if_neg e] at g
      have g' : (nth P.lowN (nth P.dcls l.val - 2) : ℝ) ≤ nth P.lowD (nth P.dcls l.val - 2) * (0 : ℝ) := by
        exact_mod_cast g
      have := mul_nonneg (Nat.cast_nonneg (nth P.lowD (nth P.dcls l.val - 2)) : (0 : ℝ) ≤ _) hh0
      linarith

end

/-! ## What the library needs from the certificates -/

/-- The energy exceeds `35 / 2` on every leaf of the list `l`. -/
def ExclLeaves (l : List Leaf) : Prop :=
  ∀ L ∈ l, ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InLeaf L y → (35 : ℝ) / 2 < energyE y

theorem exclLeaves_nil : ExclLeaves [] := fun _ hc => absurd hc List.not_mem_nil

theorem exclLeaves_cons {a : Leaf} {l : List Leaf}
    (ha : ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InLeaf a y → (35 : ℝ) / 2 < energyE y) (hl : ExclLeaves l) :
    ExclLeaves (a :: l) := by
  intro c hc y hy
  rcases List.mem_cons.1 hc with rfl | h
  · exact ha y hy
  · exact hl c h y hy

/-- **The theorem of a virtual-root certificate excludes a leaf of the core.** -/
theorem exclLeaf_of_cert {P : Par} {heads : List RecH} {L : Leaf} (hf : fitsLeaf P heads L)
    (hE : ∀ {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)}, InPieceS P heads x e f →
      (35 : ℝ) / 2 < ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2) :
    ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InLeaf L y → (35 : ℝ) / 2 < energyE y :=
  fun _ h => hE (inPieceS_of_leaf h hf)

/-- The contacts of a labelled configuration (`thm:inner` (ii)): the pairs `A`, `B` are antipodal, their points
are orthogonal to each other and to the ring points, and the inner product `t` of two ring points satisfies
`4 t² + 2 t - 1 = 0`. -/
def Contacts (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop :=
  inner ℝ (y 0) (y 1) = -1 ∧ inner ℝ (y 2) (y 3) = -1
    ∧ (∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → inner ℝ (y i) (y j) = 0)
    ∧ (∀ i j : Fin 9, i.val < 4 → 4 ≤ j.val → inner ℝ (y i) (y j) = 0)
    ∧ (∀ i j : Fin 9, 4 ≤ i.val → i < j → 4 * inner ℝ (y i) (y j) ^ 2 + 2 * inner ℝ (y i) (y j) - 1 = 0)

/-- **The inner piece** (`thm:inner`): on the leaf `I` the energy is at least `35 / 2`, and a configuration with
the energy `35 / 2` has the contacts. -/
def InnerOK : Prop :=
  ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InLeaf Leaf.I y →
    (35 : ℝ) / 2 ≤ energyE y ∧ (energyE y ≤ 35 / 2 → Contacts y)

/-- **The theorems of the sharp certificate give the statement on the inner piece.** -/
theorem innerOK_of_cert {P : Par} {heads : List RecH} (hf : fitsLeaf P heads Leaf.I)
    (hE : ∀ {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)}, InPieceS P heads x e f →
      (35 : ℝ) / 2 ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2)
    (hK : ∀ {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)}, InPieceS P heads x e f →
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 ≤ 35 / 2 → Contacts x) : InnerOK :=
  fun _ h => ⟨hE (inPieceS_of_leaf h hf), fun hle => hK (inPieceS_of_leaf h hf) hle⟩

/-- info: 'S3N9.inPieceS_of_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inPieceS_of_leaf

end S3N9
