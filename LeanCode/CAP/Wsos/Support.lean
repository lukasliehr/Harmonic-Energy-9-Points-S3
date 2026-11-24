module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Two inequalities for unit vectors with a nearly antipodal partner

Let `p` and `p'` be unit vectors with `⟪p, p'⟫ ≤ -c`, and let the inner products of `p'` with further
unit vectors be at most `T`. Both inequalities follow from the inequality of Cauchy and Schwarz for the
vector `p + α p'` with a number `α ≥ 0`, whose squared norm is at most `1 + α² - 2 α c`.

* `cap_witness` (the cap bound of the source, with a witness): `⟪p, y⟫ ≥ -(α T) - m` if `m ≥ 0` and
  `1 + α² - 2 α c ≤ m²`. For the best `α` the bound is the number
  `-(c T + √((1 - c²) (1 - T²)))` of the source; a rational `α` near it gives every smaller rational
  bound, and no square root or angle occurs.
* `support_witness` (the support inequality of the source): for `β > 0`,
  `⟪p, q₁⟫ + ⟪p, q₂⟫ + β ⟪q₁, q₂⟫ + β + 2 α T + (1 + α² - 2 α c) / (2 β) ≥ 0`.

The lemmas `cap_arith` and `sup_arith` are the arithmetic that the checks of the claims need: they pass
from inequalities between integers to these hypotheses with rational parameters.
-/

@[expose] public section

namespace CAP.Wsos

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_add_smul_sq (p q : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (a : ℝ) :
    ‖p + a • q‖ ^ 2 = 1 + 2 * (a * inner ℝ p q) + a ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, hp, hq, Real.norm_eq_abs, mul_one, sq_abs, one_pow]

/-- **The cap bound, with a witness.** -/
theorem cap_witness (p q y : E) (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hy : ‖y‖ = 1) {c T a m : ℝ}
    (h1 : inner ℝ p q ≤ -c) (h2 : inner ℝ q y ≤ T) (ha : 0 ≤ a) (hm : 0 ≤ m)
    (hw : 1 + a ^ 2 - 2 * a * c ≤ m ^ 2) : -(a * T) - m ≤ inner ℝ p y := by
  have e1 := norm_add_smul_sq p q hp hq a
  have h3 : a * inner ℝ p q ≤ a * -c := mul_le_mul_of_nonneg_left h1 ha
  have h4 : a * inner ℝ q y ≤ a * T := mul_le_mul_of_nonneg_left h2 ha
  have hsq : ‖p + a • q‖ ^ 2 ≤ m ^ 2 := by
    rw [e1]
    linarith
  have hle : ‖p + a • q‖ ≤ m := by
    by_contra hcon
    have hlt : m < ‖p + a • q‖ := not_le.mp hcon
    have h5 : m * m < ‖p + a • q‖ * ‖p + a • q‖ := mul_self_lt_mul_self hm hlt
    rw [pow_two, pow_two] at hsq
    linarith
  have hcs : |inner ℝ (p + a • q) y| ≤ ‖p + a • q‖ * ‖y‖ := abs_real_inner_le_norm _ _
  rw [hy, mul_one] at hcs
  have e : inner ℝ (p + a • q) y = inner ℝ p y + a * inner ℝ q y := by
    rw [inner_add_left, real_inner_smul_left]
  have h6 := (abs_le.mp hcs).1
  rw [e] at h6
  linarith

/-- **The support inequality.** -/
theorem support_witness (p p' q1 q2 : E) (hp : ‖p‖ = 1) (hp' : ‖p'‖ = 1) (hq1 : ‖q1‖ = 1) (hq2 : ‖q2‖ = 1)
    {c T a b : ℝ} (h0 : inner ℝ p p' ≤ -c) (h1 : inner ℝ p' q1 ≤ T) (h2 : inner ℝ p' q2 ≤ T)
    (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ inner ℝ p q1 + inner ℝ p q2 + b * inner ℝ q1 q2 + b + 2 * a * T + (1 + a ^ 2 - 2 * a * c) / (2 * b) := by
  have ew := norm_add_smul_sq p p' hp hp' a
  have ev : ‖q1 + q2‖ ^ 2 = 2 + 2 * inner ℝ q1 q2 := by
    rw [norm_add_sq_real, hq1, hq2]
    ring
  have ei : inner ℝ (p + a • p') (q1 + q2)
      = inner ℝ p q1 + inner ℝ p q2 + a * (inner ℝ p' q1 + inner ℝ p' q2) := by
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left]
    ring
  have hcs : |inner ℝ (p + a • p') (q1 + q2)| ≤ ‖p + a • p'‖ * ‖q1 + q2‖ := abs_real_inner_le_norm _ _
  have hlow := (abs_le.mp hcs).1
  rw [ei] at hlow
  have h3 : a * inner ℝ p p' ≤ a * -c := mul_le_mul_of_nonneg_left h0 ha
  have h4 : a * (inner ℝ p' q1 + inner ℝ p' q2) ≤ a * (2 * T) := mul_le_mul_of_nonneg_left (by linarith) ha
  have f1 : ‖p + a • p'‖ ^ 2 ≤ 1 + a ^ 2 - 2 * a * c := by
    rw [ew]
    linarith
  have f3 : -(‖p + a • p'‖ * ‖q1 + q2‖) ≤ inner ℝ p q1 + inner ℝ p q2 + 2 * a * T := by linarith
  have g1 := mul_le_mul_of_nonneg_left f3 (by positivity : (0 : ℝ) ≤ 2 * b)
  have g2 : b ^ 2 * ‖q1 + q2‖ ^ 2 = b ^ 2 * (2 + 2 * inner ℝ q1 q2) := by rw [ev]
  have f4 : 0 ≤ (b * ‖q1 + q2‖ - ‖p + a • p'‖) ^ 2 := sq_nonneg _
  have key : 0 ≤ 2 * b * (inner ℝ p q1 + inner ℝ p q2 + b * inner ℝ q1 q2 + b + 2 * a * T)
      + (1 + a ^ 2 - 2 * a * c) := by
    nlinarith [g1, g2, f1, f4]
  have h2b : (0 : ℝ) < 2 * b := by positivity
  have hd := div_nonneg key h2b.le
  rw [add_div, mul_div_cancel_left₀ _ h2b.ne'] at hd
  exact hd

/-! ## The arithmetic of the checks -/

/-- From the two integer inequalities of the check of a cap bound to the hypotheses of `cap_witness`:
`jl / jd` is the bound, `lp / lq` the witness, `tp / tq` the number `T`, and `hc / hd` the number `c`. -/
theorem cap_arith {jl jd lp lq tp tq hc hd : ℝ} (hjd : 0 < jd) (hlq : 0 < lq) (htq : 0 < tq) (hhd : 0 < hd)
    (h1 : 0 ≤ -jl * lq * tq - lp * tp * jd)
    (h2 : (lq ^ 2 * hd + lp ^ 2 * hd - 2 * lp * lq * hc) * (jd ^ 2 * tq ^ 2)
      ≤ (-jl * lq * tq - lp * tp * jd) ^ 2 * hd) :
    ∃ m : ℝ, 0 ≤ m ∧ 1 + (lp / lq) ^ 2 - 2 * (lp / lq) * (hc / hd) ≤ m ^ 2
      ∧ jl / jd = -(lp / lq * (tp / tq)) - m := by
  have hD : 0 < jd * lq * tq := by positivity
  refine ⟨(-jl * lq * tq - lp * tp * jd) / (jd * lq * tq), div_nonneg h1 hD.le, ?_, ?_⟩
  · have e : 1 + (lp / lq) ^ 2 - 2 * (lp / lq) * (hc / hd)
        = (lq ^ 2 * hd + lp ^ 2 * hd - 2 * lp * lq * hc) / (lq ^ 2 * hd) := by
      field_simp
    rw [e, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 := mul_le_mul_of_nonneg_right h2 (sq_nonneg lq)
    nlinarith [h3]
  · field_simp
    ring

/-- From the integer inequality of the check of a support cut to the bound for its constant:
`B / k` is `β`, `G / k` the constant, `ap / aq` the witness `α`. -/
theorem sup_arith {k B G ap aq tp tq hc hd : ℝ} (hk : 0 < k) (hB : 0 < B) (haq : 0 < aq) (htq : 0 < tq)
    (hhd : 0 < hd)
    (h : 2 * B ^ 2 * aq ^ 2 * tq * hd + k ^ 2 * (aq ^ 2 + ap ^ 2) * tq * hd + 4 * ap * aq * B * tp * k * hd
      ≤ 2 * B * G * aq ^ 2 * tq * hd + 2 * k ^ 2 * ap * aq * hc * tq) :
    B / k + 2 * (ap / aq) * (tp / tq) + (1 + (ap / aq) ^ 2 - 2 * (ap / aq) * (hc / hd)) / (2 * (B / k)) ≤ G / k := by
  have e : B / k + 2 * (ap / aq) * (tp / tq) + (1 + (ap / aq) ^ 2 - 2 * (ap / aq) * (hc / hd)) / (2 * (B / k))
      = (2 * B ^ 2 * aq ^ 2 * tq * hd + k ^ 2 * (aq ^ 2 + ap ^ 2) * tq * hd + 4 * ap * aq * B * tp * k * hd
          - 2 * k ^ 2 * ap * aq * hc * tq) / (2 * B * k * aq ^ 2 * tq * hd) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) hk]
  nlinarith [mul_le_mul_of_nonneg_right h hk.le]

end CAP.Wsos
