module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.Linarith
public import CAP.Schema.LP.Gegenbauer4
public import CAP.Schema.ThreePoint.Triples

/-!
# Schema S1 on `S³`: the linear programming bound with a marked pair

Let `E (x) = ∑ i < j, 1 / ‖x i - x j‖ ^ 2` be the harmonic energy of `n` distinct points of the unit sphere of
`ℝ⁴`, and let `U k` be the Chebyshev polynomials of the second kind, `U 0 = 1`, `U 1 = 2 t`,
`U 2 = 4 t ^ 2 - 1`, `U 3 = 8 t ^ 3 - 4 t`. For numbers `g0, g1, g2, g3` with `g1, g2, g3 ≥ 0` put
`g = g0 U 0 + g1 U 1 + g2 U 2 + g3 U 3` (`gpoly`).

`lp_marked`: suppose that `(2 - 2 t) g (t) ≤ 1` on `[-1, 1]` and that `(2 - 2 t) (g (t) + χ) ≤ 1` on `[T, 1]`.
If some pair of distinct points has an inner product of at least `T`, then

  `E (x) ≥ (n ^ 2 g0 - n g (1)) / 2 + χ`.

The proof is that of Delsarte, Goethals, Seidel and Yudin: `∑ i j, U k ⟪x i, x j⟫ ≥ 0` for `k = 1, 2, 3`
(`M1_nonneg`, `M2_nonneg`, `M3_nonneg`, from the sums of squares of `Gegenbauer4.lean` in the coordinates
of an orthonormal basis), so `∑ i j, g ⟪x i, x j⟫ ≥ n ^ 2 g0`; the diagonal contributes `n g (1)`; every
pair of distinct points satisfies `g ≤ 1 / (2 - 2 t)`, and the marked pair satisfies `g + χ ≤ 1 / (2 - 2 t)`.
-/

@[expose] public section

namespace CAP.LP

open Finset

/-- The inner product of `ℝ⁴` in the coordinates of the standard basis. -/
theorem coords4 : ∃ p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4) → ℝ, ∀ y z : EuclideanSpace ℝ (Fin 4),
    inner ℝ y z = p0 y * p0 z + p1 y * p1 z + p2 y * p2 z + p3 y * p3 z := by
  refine ⟨fun y => inner ℝ (EuclideanSpace.basisFun (Fin 4) ℝ 0) y, fun y => inner ℝ (EuclideanSpace.basisFun (Fin 4) ℝ 1) y,
    fun y => inner ℝ (EuclideanSpace.basisFun (Fin 4) ℝ 2) y, fun y => inner ℝ (EuclideanSpace.basisFun (Fin 4) ℝ 3) y,
    fun y z => ?_⟩
  have h := (EuclideanSpace.basisFun (Fin 4) ℝ).sum_inner_mul_inner y z
  rw [Fin.sum_univ_four, real_inner_comm (EuclideanSpace.basisFun (Fin 4) ℝ 0) y,
    real_inner_comm (EuclideanSpace.basisFun (Fin 4) ℝ 1) y, real_inner_comm (EuclideanSpace.basisFun (Fin 4) ℝ 2) y,
    real_inner_comm (EuclideanSpace.basisFun (Fin 4) ℝ 3) y] at h
  exact h.symm

section Kernels

variable {ι : Type*} [Fintype ι] (x : ι → EuclideanSpace ℝ (Fin 4))

/-- `∑ i j, U 1 ⟪x i, x j⟫ ≥ 0` -/
theorem M1_nonneg : 0 ≤ ∑ i, ∑ j, 2 * inner ℝ (x i) (x j) := by
  obtain ⟨p0, p1, p2, p3, h⟩ := coords4
  have key := u_quad_nonneg_1 (fun _ : ι => (1 : ℝ)) (fun i => p0 (x i)) (fun i => p1 (x i)) (fun i => p2 (x i))
    (fun i => p3 (x i))
  refine le_of_le_of_eq key (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_)
  show (1 : ℝ) * 1 * (2 * (p0 (x i) * p0 (x j) + p1 (x i) * p1 (x j) + p2 (x i) * p2 (x j) + p3 (x i) * p3 (x j))) = _
  rw [h (x i) (x j)]
  ring

/-- The squares of the coordinates of a unit vector add up to `1`. -/
theorem coords_unit {p0 p1 p2 p3 : EuclideanSpace ℝ (Fin 4) → ℝ}
    (h : ∀ y z : EuclideanSpace ℝ (Fin 4), inner ℝ y z = p0 y * p0 z + p1 y * p1 z + p2 y * p2 z + p3 y * p3 z)
    {y : EuclideanSpace ℝ (Fin 4)} (hy : ‖y‖ = 1) : p0 y ^ 2 + p1 y ^ 2 + p2 y ^ 2 + p3 y ^ 2 = 1 := by
  have e := h y y
  rw [real_inner_self_eq_norm_sq, hy] at e
  linarith

/-- `∑ i j, U 2 ⟪x i, x j⟫ ≥ 0` for points of the unit sphere. -/
theorem M2_nonneg (hu : ∀ i, ‖x i‖ = 1) : 0 ≤ ∑ i, ∑ j, (4 * inner ℝ (x i) (x j) ^ 2 - 1) := by
  obtain ⟨p0, p1, p2, p3, h⟩ := coords4
  have key := u_quad_nonneg_2 (fun _ : ι => (1 : ℝ)) (fun i => p0 (x i)) (fun i => p1 (x i)) (fun i => p2 (x i))
    (fun i => p3 (x i))
  refine le_of_le_of_eq key (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_)
  show (1 : ℝ) * 1 * (4 * (p0 (x i) * p0 (x j) + p1 (x i) * p1 (x j) + p2 (x i) * p2 (x j) + p3 (x i) * p3 (x j)) ^ 2
    - (p0 (x i) ^ 2 + p1 (x i) ^ 2 + p2 (x i) ^ 2 + p3 (x i) ^ 2)
      * (p0 (x j) ^ 2 + p1 (x j) ^ 2 + p2 (x j) ^ 2 + p3 (x j) ^ 2)) = _
  rw [h (x i) (x j), coords_unit h (hu i), coords_unit h (hu j)]
  ring

/-- `∑ i j, U 3 ⟪x i, x j⟫ ≥ 0` for points of the unit sphere. -/
theorem M3_nonneg (hu : ∀ i, ‖x i‖ = 1) :
    0 ≤ ∑ i, ∑ j, (8 * inner ℝ (x i) (x j) ^ 3 - 4 * inner ℝ (x i) (x j)) := by
  obtain ⟨p0, p1, p2, p3, h⟩ := coords4
  have key := u_quad_nonneg_3 (fun _ : ι => (1 : ℝ)) (fun i => p0 (x i)) (fun i => p1 (x i)) (fun i => p2 (x i))
    (fun i => p3 (x i))
  refine le_of_le_of_eq key (sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_)
  show (1 : ℝ) * 1 * (8 * (p0 (x i) * p0 (x j) + p1 (x i) * p1 (x j) + p2 (x i) * p2 (x j) + p3 (x i) * p3 (x j)) ^ 3
    - 4 * (p0 (x i) * p0 (x j) + p1 (x i) * p1 (x j) + p2 (x i) * p2 (x j) + p3 (x i) * p3 (x j))
      * ((p0 (x i) ^ 2 + p1 (x i) ^ 2 + p2 (x i) ^ 2 + p3 (x i) ^ 2)
        * (p0 (x j) ^ 2 + p1 (x j) ^ 2 + p2 (x j) ^ 2 + p3 (x j) ^ 2))) = _
  rw [h (x i) (x j), coords_unit h (hu i), coords_unit h (hu j)]
  ring

end Kernels

/-- The polynomial `g0 U 0 + g1 U 1 + g2 U 2 + g3 U 3`. -/
def gpoly (g0 g1 g2 g3 t : ℝ) : ℝ := g0 + g1 * (2 * t) + g2 * (4 * t ^ 2 - 1) + g3 * (8 * t ^ 3 - 4 * t)

theorem gpoly_one (g0 g1 g2 g3 : ℝ) : gpoly g0 g1 g2 g3 1 = g0 + 2 * g1 + 3 * g2 + 4 * g3 := by
  unfold gpoly
  ring

section Bound

variable {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 4))

/-- The sum of `g` over all pairs of indices is at least `n ^ 2 * g0`. -/
theorem sum_gpoly_ge (hu : ∀ i, ‖x i‖ = 1) {g0 g1 g2 g3 : ℝ} (h1 : 0 ≤ g1) (h2 : 0 ≤ g2) (h3 : 0 ≤ g3) :
    (n : ℝ) ^ 2 * g0 ≤ ∑ i, ∑ j, gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) := by
  have e : ∑ i, ∑ j, gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j))
      = (n : ℝ) ^ 2 * g0 + g1 * ∑ i, ∑ j, 2 * inner ℝ (x i) (x j)
        + g2 * ∑ i, ∑ j, (4 * inner ℝ (x i) (x j) ^ 2 - 1)
        + g3 * ∑ i, ∑ j, (8 * inner ℝ (x i) (x j) ^ 3 - 4 * inner ℝ (x i) (x j)) := by
    unfold gpoly
    simp only [sum_add_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [e]
  have a1 := mul_nonneg h1 (M1_nonneg x)
  have a2 := mul_nonneg h2 (M2_nonneg x hu)
  have a3 := mul_nonneg h3 (M3_nonneg x hu)
  linarith

/-- A double sum is the sum of its diagonal and of its terms off the diagonal. -/
theorem sum_diag_add (G : Fin n → Fin n → ℝ) :
    ∑ i, ∑ j, G i j = ∑ i, G i i + ∑ i, ∑ j, if i ≠ j then G i j else 0 := by
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  have e : ∀ j, G i j = (if i = j then G i j else 0) + (if i ≠ j then G i j else 0) := by
    intro j
    by_cases h : i = j
    · simp [h]
    · simp [h]
  rw [sum_congr rfl fun j _ => e j, sum_add_distrib, sum_ite_eq]
  simp

/-- **The linear programming bound on `S³` with a marked pair.** -/
theorem lp_marked (hu : ∀ i, ‖x i‖ = 1) (hx : Function.Injective x) {g0 g1 g2 g3 χ T : ℝ} (h1 : 0 ≤ g1)
    (h2 : 0 ≤ g2) (h3 : 0 ≤ g3)
    (hg : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → 0 ≤ 1 - (2 - 2 * t) * gpoly g0 g1 g2 g3 t)
    (hc : ∀ t : ℝ, T ≤ t → t ≤ 1 → 0 ≤ 1 - (2 - 2 * t) * (gpoly g0 g1 g2 g3 t + χ))
    {i0 j0 : Fin n} (h0 : i0 ≠ j0) (hT : T ≤ inner ℝ (x i0) (x j0)) :
    ((n : ℝ) ^ 2 * g0 - n * gpoly g0 g1 g2 g3 1) / 2 + χ
      ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 := by
  -- the inner product of two distinct points
  have hlt : ∀ i j, i ≠ j → inner ℝ (x i) (x j) < 1 := fun i j hij =>
    (inner_lt_one_iff_real_of_norm_eq_one (hu i) (hu j)).mpr fun e => hij (hx e)
  have hge : ∀ i j, -1 ≤ inner ℝ (x i) (x j) := by
    intro i j
    have h := (abs_le.mp (abs_real_inner_le_norm (x i) (x j))).1
    rw [hu i, hu j] at h
    linarith
  have hn : ∀ i j, ‖x i - x j‖ ^ 2 = 2 - 2 * inner ℝ (x i) (x j) := by
    intro i j
    rw [norm_sub_sq_real, hu i, hu j]
    ring
  -- the difference of the potential and of `g` at a pair of distinct points
  have hd : ∀ i j, i ≠ j →
      0 ≤ 1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) := by
    intro i j hij
    have hpos : (0 : ℝ) < 2 - 2 * inner ℝ (x i) (x j) := by linarith [hlt i j hij]
    have h := hg _ (hge i j) (hlt i j hij).le
    rw [hn, sub_nonneg, le_div_iff₀ hpos]
    linarith
  have hm : ∀ i j, i ≠ j → T ≤ inner ℝ (x i) (x j) →
      χ ≤ 1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) := by
    intro i j hij hT
    have hpos : (0 : ℝ) < 2 - 2 * inner ℝ (x i) (x j) := by linarith [hlt i j hij]
    have h := hc _ hT (hlt i j hij).le
    rw [hn, le_sub_iff_add_le, le_div_iff₀ hpos]
    linarith
  -- the sum of the differences over the ordered pairs of distinct points is at least `2 χ`
  have hD : 2 * χ ≤ ∑ i, ∑ j, if i ≠ j then
      1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0 := by
    have hnn : ∀ i j, 0 ≤ (if i ≠ j then
        1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0) := by
      intro i j
      by_cases h : i = j
      · simp [h]
      · rw [if_pos h]
        exact hd i j h
    have hrow : ∀ i, 0 ≤ ∑ j, if i ≠ j then
        1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0 := fun i => sum_nonneg fun j _ => hnn i j
    have r1 : χ ≤ ∑ j, if i0 ≠ j then
        1 / ‖x i0 - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i0) (x j)) else 0 := by
      refine le_trans ?_ (single_le_sum (fun j _ => hnn i0 j) (mem_univ j0))
      rw [if_pos h0]
      exact hm i0 j0 h0 hT
    have r2 : χ ≤ ∑ j, if j0 ≠ j then
        1 / ‖x j0 - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x j0) (x j)) else 0 := by
      refine le_trans ?_ (single_le_sum (fun j _ => hnn j0 j) (mem_univ i0))
      rw [if_pos (Ne.symm h0)]
      refine hm j0 i0 (Ne.symm h0) ?_
      rw [real_inner_comm]
      exact hT
    have hsplit := add_sum_erase univ (fun i => ∑ j, if i ≠ j then
        1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0) (mem_univ i0)
    have r3 := single_le_sum (s := univ.erase i0) (fun i _ => hrow i) (mem_erase.mpr ⟨Ne.symm h0, mem_univ j0⟩)
    linarith
  -- the sum of `g` over the ordered pairs of distinct points
  have hG := sum_gpoly_ge x hu (g0 := g0) h1 h2 h3
  rw [sum_diag_add] at hG
  have hdiag : ∑ i : Fin n, gpoly g0 g1 g2 g3 (inner ℝ (x i) (x i)) = n * gpoly g0 g1 g2 g3 1 := by
    rw [sum_congr rfl fun i _ => by rw [real_inner_self_eq_norm_sq, hu i, one_pow], sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hdiag] at hG
  -- the energy
  have hE := CAP.ThreePoint.sum_ne_eq_two_mul_sum_lt (fun i j => 1 / ‖x i - x j‖ ^ 2) (fun i j => by rw [norm_sub_rev])
  have hsub : (∑ i, ∑ j, if i ≠ j then (1 : ℝ) / ‖x i - x j‖ ^ 2 else 0)
      = (∑ i, ∑ j, if i ≠ j then gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0)
        + ∑ i, ∑ j, if i ≠ j then
          1 / ‖x i - x j‖ ^ 2 - gpoly g0 g1 g2 g3 (inner ℝ (x i) (x j)) else 0 := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : i = j
    · simp [h]
    · rw [if_pos h, if_pos h, if_pos h]
      ring
  linarith

end Bound

end CAP.LP
