module

public import CAP.Wsos.Minorant

/-!
# The theorem of a typed certificate: a bound for the energy

Let `E (x) = ∑ i < j, 1 / ‖x i - x j‖ ^ 2` be the energy of points of the unit sphere of `ℝ⁴`.

`energy_gt`: let the data of a typed certificate satisfy

* `CertHolds`: the statements of the checkers `checkTy` and `gramOk` and the conditions on the tables,
* `domOk`: the domain of the checker contains the domain that the source declares,
* `Minorant`: the sign conditions, which follow from the check `signsOk`,
* `boundOk`: the bound of the certificate exceeds `tp / tq`.

Then `tp / tq < E (x)` for all labelled distinct points of the sphere in the domain of the source
(`InSource`): the inner product of every pair lies in the interval of its pair type, and the inner
products of every triple satisfy the further inequalities of its triple type.

The proof combines `typed_bound` (the theorem of the schema) with `inDomain_of_source`, bounds every pair
polynomial by the potential (`pairH_le`), and evaluates the bound (`boundOk_sound`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

section Points

variable {P : Params} {C : Cert} {xs : List TyX} {Dm : Dom} {sP : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  {cls : ι → ℕ} {x : ι → EuclideanSpace ℝ (Fin 4)}

omit [DecidableEq ι] in
/-- The pair polynomial of two points is at most the potential, in the unit of the checker. -/
theorem pairH_le (hmin : Minorant P C Dm sP) (hS : InSource P.q C Dm cls x) {i j : ι} (hij : i ≠ j) :
    pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j)
      ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * (1 / ‖x i - x j‖ ^ 2) := by
  have L := hS.lab
  have key : ∀ i j : ι, i ≠ j → cls i ≤ cls j →
      pairH P C (cls i) (cls j) (wv P.m x i j) ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * (1 / ‖x i - x j‖ ^ 2) := by
    intro i j hij hle
    obtain ⟨hlo, hhi⟩ := hS.iv i j hij hle
    have hH := hmin _ (L.lt i) _ (L.lt j) hle (L.pcnt_pos hij) _ hlo hhi
    have ht1 : inner ℝ (x i) (x j) < 1 :=
      (inner_lt_one_iff_real_of_norm_eq_one (hS.unit i) (hS.unit j)).mpr fun e => hij (hS.inj e)
    have hn : ‖x i - x j‖ ^ 2 = 2 - 2 * inner ℝ (x i) (x j) := by
      rw [norm_sub_sq_real, hS.unit i, hS.unit j]
      ring
    have hpos : (0 : ℝ) < 2 - 2 * inner ℝ (x i) (x j) := by linarith
    have h2 : spolyV P.wP (1 : ℝ) (inner ℝ (x i) (x j)) P.D (C.H (cls i) (cls j))
        ≤ 2 ^ sP / (2 - 2 * inner ℝ (x i) (x j)) := by
      rw [le_div_iff₀ hpos, mul_comm]
      exact hH
    have h3 : (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * spolyV P.wP (1 : ℝ) (inner ℝ (x i) (x j)) P.D (C.H (cls i) (cls j)))
        ≤ (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * (2 ^ sP / (2 - 2 * inner ℝ (x i) (x j)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)
    have e : (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * (1 / (2 - 2 * inner ℝ (x i) (x j)))
        = (2 : ℝ) ^ P.aP * (((2 : ℝ) ^ P.m) ^ P.D * (2 ^ sP / (2 - 2 * inner ℝ (x i) (x j)))) := by
      rw [pow_add, pow_add, pow_mul]
      ring
    unfold pairH wv
    rw [spolyV_hom, hn, e]
    exact h3
  rcases le_total (cls i) (cls j) with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    exact key i j hij hle
  · have h := key j i (Ne.symm hij) hle
    rw [wv_comm P.m x i j, norm_sub_rev] at h
    rw [min_eq_right hle, max_eq_left hle]
    exact h

/-- **The energy of points in the domain of a typed certificate exceeds `tp / tq`.** The sum runs over the
ordered pairs of distinct points, hence the factor `1 / 2`. -/
theorem energy_gt {M tp tq : ℕ} (H : CertHolds P C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant P C Dm sP) (hb : boundOk P C xs sP M tp tq = true) (hS : InSource P.q C Dm cls x) :
    (tp : ℝ) / tq < (∑ i, ∑ j, if i ≠ j then 1 / ‖x i - x j‖ ^ 2 else 0) / 2 := by
  have hD := inDomain_of_source H hdom hS
  have hT : dsum3 (fun i j k => tyC P C (typeOf xs (cls i) (cls j) (cls k)))
      ≤ 3 * (∑ i, ∑ j, if i ≠ j then
          pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j) else 0)
        + 6 * ∑ i, rootS P C (cls i) (cls i) (cls i) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) ((2 : ℝ) ^ P.m) :=
    typed_bound H hD
  have hsum : (∑ i, ∑ j, if i ≠ j then
        pairH P C (min (cls i) (cls j)) (max (cls i) (cls j)) (wv P.m x i j) else 0)
      ≤ (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * ∑ i, ∑ j, if i ≠ j then 1 / ‖x i - x j‖ ^ 2 else 0 := by
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_pos hij, if_pos hij]
      exact pairH_le hmin hS hij
  refine boundOk_sound H hb hS.lab _ ?_
  have e : 6 * (2 : ℝ) ^ (P.m * P.D + P.aP + sP) * ((∑ i, ∑ j, if i ≠ j then 1 / ‖x i - x j‖ ^ 2 else 0) / 2)
      = 3 * ((2 : ℝ) ^ (P.m * P.D + P.aP + sP) * ∑ i, ∑ j, if i ≠ j then 1 / ‖x i - x j‖ ^ 2 else 0) := by ring
  rw [e]
  linarith

end Points

/-- The same for points with the indices `Fin n`, with the sum over the pairs `i < j`. -/
theorem energy_gt_fin {P : Params} {C : Cert} {xs : List TyX} {Dm : Dom} {sP M tp tq n : ℕ} {cls : Fin n → ℕ}
    {x : Fin n → EuclideanSpace ℝ (Fin 4)} (H : CertHolds P C xs) (hdom : domOk P C Dm xs = true)
    (hmin : Minorant P C Dm sP) (hb : boundOk P C xs sP M tp tq = true) (hS : InSource P.q C Dm cls x) :
    (tp : ℝ) / tq < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 := by
  have h := energy_gt H hdom hmin hb hS
  rw [sum_ne_eq_two_mul_sum_lt (fun i j => 1 / ‖x i - x j‖ ^ 2) (fun i j => by rw [norm_sub_rev]),
    mul_div_cancel_left₀ _ (two_ne_zero)] at h
  exact h

end CAP.Wsos
