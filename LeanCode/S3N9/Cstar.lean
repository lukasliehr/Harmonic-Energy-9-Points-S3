module

public import S3N9.Statement
public import CAP.VR.Sphere

/-!
# The theorem for nine points: the configuration `Cstar`

`Cstar` consists of the vertices of a regular pentagon in the plane of the first two coordinates and of the points
`±e₃`, `±e₄`. This file proves the first statement of the theorem (`lma:ECstar`, row A1 of `S3N9/README.md`):

* `onSphere_Cstar`: the points lie on the unit sphere;
* `dist_CstarN`: the squared distance of two points, from the table `dC`: `2 - 2 cos 72°` and `2 - 2 cos 144°` for
  two vertices of the pentagon, `4` for the two antipodal pairs, and `2` otherwise;
* `injective_Cstar`: the points are distinct;
* `energy_Cstar`: the energy is `35 / 2`.

The values `cos 72° = (√5 - 1) / 4` and `cos 144° = -(√5 + 1) / 4` follow from `Real.cos_pi_div_five`.
-/

@[expose] public section

namespace S3N9

open Real

/-- `cos 72°`. -/
noncomputable def cPlus : ℝ := (√5 - 1) / 4

/-- `cos 144°`. -/
noncomputable def cMinus : ℝ := -(√5 + 1) / 4

theorem sqrt5_sq : (√5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)

theorem cos_a : cos (2 * π / 5) = cPlus := by
  have e : 2 * π / 5 = 2 * (π / 5) := by ring
  rw [e, Real.cos_two_mul, Real.cos_pi_div_five]
  unfold cPlus
  linear_combination (1 / 8) * sqrt5_sq

theorem cos_2a : cos (2 * (2 * π / 5)) = cMinus := by
  rw [Real.cos_two_mul, cos_a]
  unfold cPlus cMinus
  linear_combination (1 / 8) * sqrt5_sq

theorem cos_3a : cos (3 * (2 * π / 5)) = cMinus := by
  have e : 3 * (2 * π / 5) = 2 * π - 2 * (2 * π / 5) := by ring
  rw [e, Real.cos_two_pi_sub, cos_2a]

theorem cos_4a : cos (4 * (2 * π / 5)) = cPlus := by
  have e : 4 * (2 * π / 5) = 2 * π - 2 * π / 5 := by ring
  rw [e, Real.cos_two_pi_sub, cos_a]

/-- The inner product of two vertices of the pentagon whose indices differ by `d`. -/
noncomputable def cP (d : ℕ) : ℝ := if d = 1 ∨ d = 4 then cPlus else cMinus

theorem cos_d : ∀ d : ℕ, 1 ≤ d → d ≤ 4 → cos ((d : ℝ) * (2 * π / 5)) = cP d := by
  intro d h1 h4
  interval_cases d
  · rw [Nat.cast_one, one_mul, cos_a]
    simp [cP]
  · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, cos_2a]
    simp [cP]
  · rw [show ((3 : ℕ) : ℝ) = 3 by norm_num, cos_3a]
    simp [cP]
  · rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, cos_4a]
    simp [cP]

/-- The squared distance of two adjacent vertices of the pentagon. -/
noncomputable def dP : ℝ := 2 - 2 * cPlus

/-- The squared distance of two vertices of the pentagon that are not adjacent. -/
noncomputable def dM : ℝ := 2 - 2 * cMinus

theorem sqrt5_lt : (√5 : ℝ) < 3 := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5) (by norm_num : (5 : ℝ) < 9)
  have e : (√9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rwa [e] at h

theorem dP_pos : 0 < dP := by
  unfold dP cPlus
  linarith [sqrt5_lt]

theorem dM_pos : 0 < dM := by
  unfold dM cMinus
  linarith [Real.sqrt_nonneg (5 : ℝ)]

theorem dP_dM : dP⁻¹ + dM⁻¹ = 1 := by
  have hp := ne_of_gt dP_pos
  have hm := ne_of_gt dM_pos
  rw [← one_div, ← one_div, div_add_div _ _ hp hm, div_eq_one_iff_eq (mul_ne_zero hp hm)]
  unfold dP dM cPlus cMinus
  linear_combination (1 / 4) * sqrt5_sq

/-- The coordinates of the points of `Cstar`, for a natural index. -/
noncomputable def CstarN (n : ℕ) : Fin 4 → ℝ :=
  if n < 5 then ![Real.cos (2 * Real.pi * n / 5), Real.sin (2 * Real.pi * n / 5), 0, 0]
  else if n = 5 then ![0, 0, 1, 0]
  else if n = 6 then ![0, 0, -1, 0]
  else if n = 7 then ![0, 0, 0, 1]
  else ![0, 0, 0, -1]

theorem Cstar_eq (n : Fin 9) : Cstar n = CstarN n.val := rfl

/-- The squared distances of the points of `Cstar`. -/
noncomputable def dC (i j : ℕ) : ℝ :=
  if j < 5 then (if j - i = 1 ∨ j - i = 4 then dP else dM)
  else if i < 5 then 2
  else if (i = 5 ∧ j = 6) ∨ (i = 7 ∧ j = 8) then 4 else 2

theorem dist_CstarN : ∀ i j : ℕ, i < j → j < 9 → ∑ k, (CstarN i k - CstarN j k) ^ 2 = dC i j := by
  intro i j hij hj
  by_cases hj5 : j < 5
  · have hi5 : i < 5 := by omega
    have e : cos (2 * π * i / 5) * cos (2 * π * j / 5) + sin (2 * π * i / 5) * sin (2 * π * j / 5)
        = cP (j - i) := by
      rw [← Real.cos_sub]
      have e1 : 2 * π * (i : ℝ) / 5 - 2 * π * (j : ℝ) / 5 = -(((j - i : ℕ) : ℝ) * (2 * π / 5)) := by
        rw [Nat.cast_sub (le_of_lt hij)]
        ring
      rw [e1, Real.cos_neg]
      exact cos_d (j - i) (by omega) (by omega)
    have e2 : dC i j = 2 - 2 * cP (j - i) := by
      unfold dC cP dP dM
      rw [if_pos hj5]
      split_ifs <;> rfl
    rw [e2, ← e]
    simp only [CstarN, if_pos hi5, if_pos hj5, Fin.sum_univ_four]
    simp
    nlinarith [Real.cos_sq_add_sin_sq (2 * π * (i : ℝ) / 5), Real.cos_sq_add_sin_sq (2 * π * (j : ℝ) / 5)]
  · by_cases hi5 : i < 5
    · have e2 : dC i j = 2 := by
        unfold dC
        rw [if_neg hj5, if_pos hi5]
      rw [e2]
      have hc := Real.cos_sq_add_sin_sq (2 * π * (i : ℝ) / 5)
      interval_cases j <;> simp [CstarN, hi5, Fin.sum_univ_four] <;> nlinarith
    · interval_cases j <;> interval_cases i <;>
        first
        | omega
        | (simp [CstarN, dC, Fin.sum_univ_four]; norm_num)

theorem dC_pos : ∀ i j : ℕ, i < j → j < 9 → 0 < dC i j := by
  intro i j hij hj
  unfold dC
  split_ifs
  · exact dP_pos
  · exact dM_pos
  · norm_num
  · norm_num
  · norm_num

/-- **The points of `Cstar` lie on the unit sphere.** -/
theorem onSphere_Cstar : OnSphere Cstar := by
  intro i
  rw [Cstar_eq]
  have hi := i.isLt
  obtain ⟨n, hn⟩ : ∃ n, n = i.val := ⟨_, rfl⟩
  rw [← hn] at hi ⊢
  by_cases h5 : n < 5
  · simp [CstarN, h5, Fin.sum_univ_four]
  · interval_cases n <;> simp [CstarN, Fin.sum_univ_four]

/-- **The points of `Cstar` are distinct.** -/
theorem injective_Cstar : Function.Injective Cstar := by
  intro i j hij
  by_contra hne
  have key : ∀ a b : Fin 9, a < b → Cstar a ≠ Cstar b := by
    intro a b hab e
    have h1 := dist_CstarN a.val b.val hab b.isLt
    rw [← Cstar_eq, ← Cstar_eq, e] at h1
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h1
    linarith [dC_pos a.val b.val hab b.isLt]
  rcases lt_or_gt_of_ne hne with h | h
  · exact key i j h hij
  · exact key j i h hij.symm

/-- **The energy of `Cstar` is `35 / 2`** (`lma:ECstar`). -/
theorem energy_Cstar : energy Cstar = 35 / 2 := by
  unfold energy
  have e2 : ∑ i : Fin 9, ∑ j with i < j, 1 / ∑ k, (Cstar i k - Cstar j k) ^ 2
      = ∑ i : Fin 9, ∑ j ∈ Finset.univ.filter (fun j : Fin 9 => i < j), 1 / dC i.val j.val :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => by
      rw [Cstar_eq, Cstar_eq, dist_CstarN i.val j.val (Finset.mem_filter.1 hj).2 j.isLt]
  rw [e2, CAP.VR.sum_fin_pairs 9 (fun i j => 1 / dC i j)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have h := dP_dM
  norm_num [dC]
  linarith

/-- info: 'S3N9.energy_Cstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energy_Cstar

end S3N9
