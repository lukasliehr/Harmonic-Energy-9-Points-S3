module

public import CAP.Schema.LP.Sphere3

/-!
# Separation: a configuration with two close points has an energy above `35 / 2`

This is the first computational statement of the source (C1 of `S3N9/README.md`; the lemmas on the
linear programming identity, on the polynomials `h` and `h_χ`, and on the separation in Section 2 of its
paper). Let

  `g = g0 U 0 + g1 U 1 + g2 U 2 + g3 U 3`,
  `g0 = 6019524913 / 10 ^ 10`, `g1 = 1458827969 / (5 * 10 ^ 9)`, `g2 = 1020929887 / 10 ^ 10`,
  `g3 = 94829631 / (5 * 10 ^ 9)`,   `χ = 439603221 / (25 * 10 ^ 8)`,   `T = 1089 / 2000`,

with the Chebyshev polynomials `U k` of the second kind (the data of the entry `separation` of the file
of the source with the inputs of the linear programs).

* `sep_h_nonneg`: `h (t) = 1 - (2 - 2 t) g (t) ≥ 0` for all real `t`. The source writes
  `5 * 10 ^ 9 * h = zᵀ Γ z` with `z = (1, t, t ^ 2)` and a positive definite integer matrix `Γ`, whose
  leading principal minors are `1404974`, `673053090519` and `1313621984186200`. The proof here is the
  same certificate in the form of the decomposition `Γ = L D Lᵀ`, cleared of denominators: one identity
  between integer polynomials, which `ring` verifies.
* `sep_hchi_nonneg`: `h_χ (t) = 1 - (2 - 2 t) (g (t) + χ) ≥ 0` on `[T, 1]`: the Bernstein coefficients
  `β 0, …, β 4` of `15 * 10 ^ 21 * h_χ` on this interval, which the source prints, are positive; the
  identity between the two polynomials is verified by `ring`.
* `separation_bound`: nine distinct points of the unit sphere of `ℝ⁴` with a pair of inner product at least
  `T` have the energy at least `350011972239 / (2 * 10 ^ 10)`, the number `B + χ` of the source.
* `separation`: if the energy is at most `35 / 2`, then all inner products of distinct points are below `T`.

The schema theorem is `CAP.LP.lp_marked`.
-/

@[expose] public section

namespace S3N9

open Finset

/-- The polynomial `g` of the separation certificate. -/
noncomputable def sepG (t : ℝ) : ℝ :=
  CAP.LP.gpoly (6019524913 / 10 ^ 10) (1458827969 / (5 * 10 ^ 9)) (1020929887 / 10 ^ 10) (94829631 / (5 * 10 ^ 9)) t

/-- The number `χ` of the separation certificate. -/
noncomputable def sepChi : ℝ := 439603221 / (25 * 10 ^ 8)

/-- `5 * 10 ^ 9 * h` is the integer polynomial of the source. -/
theorem sep_h_eq (t : ℝ) : 5 * 10 ^ 9 * (1 - (2 - 2 * t) * sepG t)
    = 1404974 - 78079802 * t + 992955280 * t ^ 2 + 2566445452 * t ^ 3 + 1517274096 * t ^ 4 := by
  unfold sepG CAP.LP.gpoly
  ring

/-- `h ≥ 0` on the real line. -/
theorem sep_h_nonneg (t : ℝ) : 0 ≤ 1 - (2 - 2 * t) * sepG t := by
  have key : 1404974 * 673053090519 * (5 * 10 ^ 9) * (1 - (2 - 2 * t) * sepG t)
      = 673053090519 * (1404974 - 39039901 * t - 46161200 * t ^ 2) ^ 2
        + (673053090519 * t + 765888197924 * t ^ 2) ^ 2 + 1404974 * 1313621984186200 * t ^ 4 := by
    unfold sepG CAP.LP.gpoly
    ring
  have h : 0 ≤ 1404974 * 673053090519 * (5 * 10 ^ 9) * (1 - (2 - 2 * t) * sepG t) := by
    rw [key]
    positivity
  exact nonneg_of_mul_nonneg_right h (by norm_num)

/-- A polynomial of degree four with nonnegative Bernstein coefficients is nonnegative. -/
theorem bernstein4_nonneg {b0 b1 b2 b3 b4 a b : ℝ} (h0 : 0 ≤ b0) (h1 : 0 ≤ b1) (h2 : 0 ≤ b2) (h3 : 0 ≤ b3)
    (h4 : 0 ≤ b4) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ b0 * b ^ 4 + 4 * b1 * a * b ^ 3 + 6 * b2 * a ^ 2 * b ^ 2 + 4 * b3 * a ^ 3 * b + b4 * a ^ 4 := by
  positivity

/-- `h_χ ≥ 0` on `[T, 1]`. -/
theorem sep_hchi_nonneg {t : ℝ} (h1 : 1089 / 2000 ≤ t) (h2 : t ≤ 1) : 0 ≤ 1 - (2 - 2 * t) * (sepG t + sepChi) := by
  have ha : (0 : ℝ) ≤ 2000 * t - 1089 := by linarith
  have hb : (0 : ℝ) ≤ 2000 - 2000 * t := by linarith
  have key : 15 * 10 ^ 21 * 911 ^ 4 * (1 - (2 - 2 * t) * (sepG t + sepChi))
      = 13665107099317713 * (2000 - 2000 * t) ^ 4
        + 4 * 2058002975890192789125 * (2000 * t - 1089) * (2000 - 2000 * t) ^ 3
        + 6 * 4933910009123406500000 * (2000 * t - 1089) ^ 2 * (2000 - 2000 * t) ^ 2
        + 4 * 9043878680999250000000 * (2000 * t - 1089) ^ 3 * (2000 - 2000 * t)
        + 15000000000000000000000 * (2000 * t - 1089) ^ 4 := by
    unfold sepG sepChi CAP.LP.gpoly
    ring
  have h : 0 ≤ 15 * 10 ^ 21 * 911 ^ 4 * (1 - (2 - 2 * t) * (sepG t + sepChi)) := by
    rw [key]
    exact bernstein4_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha hb
  exact nonneg_of_mul_nonneg_right h (by norm_num)

/-- **The bound of the separation certificate.** -/
theorem separation_bound {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖x i‖ = 1) (hx : Function.Injective x)
    {i j : Fin 9} (hij : i ≠ j) (h : (1089 : ℝ) / 2000 ≤ inner ℝ (x i) (x j)) :
    (350011972239 : ℝ) / (2 * 10 ^ 10) ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 := by
  have hb := CAP.LP.lp_marked x hu hx (g0 := 6019524913 / 10 ^ 10) (g1 := 1458827969 / (5 * 10 ^ 9))
    (g2 := 1020929887 / 10 ^ 10) (g3 := 94829631 / (5 * 10 ^ 9)) (χ := sepChi) (T := 1089 / 2000)
    (by norm_num) (by norm_num) (by norm_num) (fun t _ _ => sep_h_nonneg t) (fun t h1 h2 => sep_hchi_nonneg h1 h2) hij h
  have e : (((9 : ℕ) : ℝ) ^ 2 * (6019524913 / 10 ^ 10)
      - ((9 : ℕ) : ℝ) * CAP.LP.gpoly (6019524913 / 10 ^ 10) (1458827969 / (5 * 10 ^ 9)) (1020929887 / 10 ^ 10)
          (94829631 / (5 * 10 ^ 9)) 1) / 2 + sepChi = 350011972239 / (2 * 10 ^ 10) := by
    rw [CAP.LP.gpoly_one]
    unfold sepChi
    norm_num
  rw [e] at hb
  exact hb

/-- **Separation.** If the energy of nine distinct points of the unit sphere of `ℝ⁴` is at most `35 / 2`,
then the inner product of every two distinct points is below `1089 / 2000`. -/
theorem separation {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖x i‖ = 1) (hx : Function.Injective x)
    (hE : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 ≤ (35 : ℝ) / 2) {i j : Fin 9} (hij : i ≠ j) :
    inner ℝ (x i) (x j) < (1089 : ℝ) / 2000 := by
  by_contra hcon
  have h := separation_bound hu hx hij (not_lt.mp hcon)
  have hlt : (35 : ℝ) / 2 < 350011972239 / (2 * 10 ^ 10) := by norm_num
  linarith

/-- info: 'S3N9.separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms S3N9.separation

end S3N9
