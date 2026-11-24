module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt

/-!
# The theorem for nine points: a near pair and the Gram–Schmidt frame

For two unit vectors `p`, `p'` with `⟪p, p'⟫ < 1` we write `r = halfLen p p'` for half the length of `p - p'`
and `d = dirOf p p'` for the unit vector `(p - p') / (2 r)`: then `⟪p, d⟫ = r`, `⟪p', d⟫ = -r` and
`r ^ 2 = (1 - ⟪p, p'⟫) / 2`.

* `abs_inner_dir_le` (part (iii) of `lma:gscell`): a unit vector `y` with `⟪p, y⟫ ≤ T` and `⟪p', y⟫ ≤ T`, for a
  pair with `1 - r ^ 2 ≤ η` and `η + T ^ 2 ≤ 1`, satisfies `|⟪y, d⟫| ≤ T √(1 - η) + √η √(1 - T ^ 2)`. The proof
  is algebraic (`cap_core`); the source argues with angles.
* `frameF e eB`: the second vector of the Gram–Schmidt frame of `e` and `eB`. `frame_unit`, `frame_orth`,
  `frame_eB`: it is a unit vector orthogonal to `e`, and `eB = s • e + c • f` with `s = ⟪e, eB⟫`,
  `c = √(1 - s ^ 2)`.
* `bessel2`, `zeta_cs`: for an orthonormal pair `e`, `f` and unit vectors `x`, `x'`:
  `⟪x, e⟫ ^ 2 + ⟪x, f⟫ ^ 2 ≤ 1` and `H ^ 2 ≤ R R'` for `H = ⟪x, x'⟫ - u u' - v v'`, `R = 1 - u ^ 2 - v ^ 2`.

This is part of row A7 of `S3N9/README.md`.
-/

@[expose] public section

namespace S3N9

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## A pair of unit vectors -/

/-- Half the length of `p - p'`, for unit vectors. -/
noncomputable def halfLen (p p' : V) : ℝ := √((1 - inner ℝ p p') / 2)

/-- The direction of `p - p'`. -/
noncomputable def dirOf (p p' : V) : V := (2 * halfLen p p')⁻¹ • (p - p')

section Pair

variable {p p' : V} (hp : ‖p‖ = 1) (hp' : ‖p'‖ = 1) (ht : inner ℝ p p' < 1)

include ht in
theorem halfLen_sq : halfLen p p' ^ 2 = (1 - inner ℝ p p') / 2 :=
  Real.sq_sqrt (by linarith)

include ht in
theorem halfLen_pos : 0 < halfLen p p' :=
  Real.sqrt_pos.2 (by linarith)

include hp hp' in
theorem inner_sub_left_pair : inner ℝ p (p - p') = 1 - inner ℝ p p' := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hp, one_pow]

include hp hp' in
theorem inner_sub_right_pair : inner ℝ p' (p - p') = inner ℝ p p' - 1 := by
  rw [inner_sub_right, real_inner_self_eq_norm_sq, hp', one_pow, real_inner_comm]

include hp hp' ht in
theorem inner_dir_left : inner ℝ p (dirOf p p') = halfLen p p' := by
  have h2 := halfLen_sq ht
  have h0 := halfLen_pos ht
  unfold dirOf
  rw [real_inner_smul_right, inner_sub_left_pair hp hp']
  field_simp
  linarith

include hp hp' ht in
theorem inner_dir_right : inner ℝ p' (dirOf p p') = -halfLen p p' := by
  have h2 := halfLen_sq ht
  have h0 := halfLen_pos ht
  unfold dirOf
  rw [real_inner_smul_right, inner_sub_right_pair hp hp']
  field_simp
  linarith

include ht in
theorem sub_eq_smul_dir : p - p' = (2 * halfLen p p') • dirOf p p' := by
  have h0 := halfLen_pos ht
  unfold dirOf
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

include hp hp' ht in
theorem inner_dir_self : inner ℝ (dirOf p p') (dirOf p p') = 1 := by
  have h2 := halfLen_sq ht
  have h0 := halfLen_pos ht
  have e1 : inner ℝ (p - p') (dirOf p p') = 2 * halfLen p p' := by
    rw [inner_sub_left, inner_dir_left hp hp' ht, inner_dir_right hp hp' ht]
    ring
  have e2 : inner ℝ (dirOf p p') (dirOf p p') = (2 * halfLen p p')⁻¹ * inner ℝ (p - p') (dirOf p p') :=
    real_inner_smul_left (p - p') (dirOf p p') ((2 * halfLen p p')⁻¹)
  rw [e2, e1, inv_mul_cancel₀ (by positivity)]

include hp hp' ht in
theorem norm_dir : ‖dirOf p p'‖ = 1 := by
  have h := inner_dir_self hp hp' ht
  rw [real_inner_self_eq_norm_sq] at h
  have h0 : 0 ≤ ‖dirOf p p'‖ := norm_nonneg _
  nlinarith

/-- The inner product of a vector with the direction of a pair. -/
theorem inner_dir (x : V) : inner ℝ x (dirOf p p') = (2 * halfLen p p')⁻¹ * (inner ℝ x p - inner ℝ x p') := by
  unfold dirOf
  rw [real_inner_smul_right, inner_sub_right]

end Pair

/-! ## The bound for the coordinate of a third point along a pair -/

/-- The algebraic core of the bound: if `r U - m W ≤ T` for `r ^ 2 + m ^ 2 = 1`, `U ^ 2 + W ^ 2 = 1` and
`m ≤ m₀`, then `U ≤ r₀ T + m₀ √(1 - T ^ 2)`. -/
theorem cap_core {r m U W T r₀ m₀ : ℝ} (hm : 0 ≤ m) (hmm : m ≤ m₀) (hr : 0 < r) (hrm : r ^ 2 + m ^ 2 = 1)
    (hr₀ : 0 ≤ r₀) (hrm₀ : r₀ ^ 2 + m₀ ^ 2 = 1) (hT : 0 ≤ T) (hmT : m₀ ^ 2 + T ^ 2 ≤ 1) (hU : 0 ≤ U)
    (hW : 0 ≤ W) (hUW : U ^ 2 + W ^ 2 = 1) (h : r * U - m * W ≤ T) : U ≤ r₀ * T + m₀ * √(1 - T ^ 2) := by
  have hm₀ : 0 ≤ m₀ := le_trans hm hmm
  have hS0 : 0 ≤ √(1 - T ^ 2) := Real.sqrt_nonneg _
  have hS2 : √(1 - T ^ 2) ^ 2 = 1 - T ^ 2 := Real.sq_sqrt (by nlinarith)
  set S := √(1 - T ^ 2) with hS
  set U₁ := r₀ * T + m₀ * S with hU₁
  set V₁ := r₀ * S - m₀ * T with hV₁
  have hV0 : 0 ≤ V₁ := by
    have h1 : (m₀ * T) ^ 2 ≤ (r₀ * S) ^ 2 := by
      have : (r₀ * S) ^ 2 - (m₀ * T) ^ 2 = 1 - m₀ ^ 2 - T ^ 2 := by
        rw [mul_pow, mul_pow, hS2]
        have : r₀ ^ 2 = 1 - m₀ ^ 2 := by linarith
        rw [this]
        ring
      linarith
    have h2 := sq_le_sq.1 h1
    rw [abs_of_nonneg (mul_nonneg hm₀ hT), abs_of_nonneg (mul_nonneg hr₀ hS0)] at h2
    rw [hV₁]
    linarith
  have hU0 : 0 ≤ U₁ := add_nonneg (mul_nonneg hr₀ hT) (mul_nonneg hm₀ hS0)
  have hUV : U₁ ^ 2 + V₁ ^ 2 = 1 := by
    have : U₁ ^ 2 + V₁ ^ 2 = (r₀ ^ 2 + m₀ ^ 2) * (T ^ 2 + S ^ 2) := by
      rw [hU₁, hV₁]
      ring
    rw [this, hrm₀, hS2]
    ring
  have hT' : r₀ * U₁ - m₀ * V₁ = T := by
    have : r₀ * U₁ - m₀ * V₁ = (r₀ ^ 2 + m₀ ^ 2) * T := by
      rw [hU₁, hV₁]
      ring
    rw [this, hrm₀, one_mul]
  have hrr : r₀ ≤ r := by
    have h1 : r₀ ^ 2 ≤ r ^ 2 := by nlinarith
    have h2 := sq_le_sq.1 h1
    rwa [abs_of_nonneg hr₀, abs_of_nonneg (le_of_lt hr)] at h2
  by_contra hcon
  rw [not_le] at hcon
  have hWV : W < V₁ := by
    have h1 : W ^ 2 < V₁ ^ 2 := by nlinarith
    have h2 := sq_lt_sq.1 h1
    rwa [abs_of_nonneg hW, abs_of_nonneg hV0] at h2
  have h1 : r * U₁ < r * U := mul_lt_mul_of_pos_left hcon hr
  have h2 : m * W ≤ m * V₁ := mul_le_mul_of_nonneg_left (le_of_lt hWV) hm
  have h3 : r₀ * U₁ ≤ r * U₁ := mul_le_mul_of_nonneg_right hrr hU0
  have h4 : m * V₁ ≤ m₀ * V₁ := mul_le_mul_of_nonneg_right hmm hV0
  linarith

/-- **The coordinate of a third point along a pair** (`lma:gscell` (iii)). -/
theorem abs_inner_dir_le {p p' y : V} (hp : ‖p‖ = 1) (hp' : ‖p'‖ = 1) (hy : ‖y‖ = 1) {η T : ℝ}
    (ht : inner ℝ p p' < 1) (hη : 1 - halfLen p p' ^ 2 ≤ η) (hη1 : η ≤ 1) (hT : 0 ≤ T) (hηT : η + T ^ 2 ≤ 1)
    (h1 : inner ℝ p y ≤ T) (h2 : inner ℝ p' y ≤ T) :
    |inner ℝ y (dirOf p p')| ≤ √(1 - η) * T + √η * √(1 - T ^ 2) := by
  have hr2 := halfLen_sq ht
  have hr0 := halfLen_pos ht
  have hdd : inner ℝ (dirOf p p') (dirOf p p') = 1 := inner_dir_self hp hp' ht
  have hdn : ‖dirOf p p'‖ = 1 := norm_dir hp hp' ht
  have hpd := inner_dir_left hp hp' ht
  have hpd' := inner_dir_right hp hp' ht
  have hsub := sub_eq_smul_dir (p := p) (p' := p') ht
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = halfLen p p' := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : V, d = dirOf p p' := ⟨_, rfl⟩
  rw [← hr] at hr2 hr0 hη hpd hpd' hsub
  rw [← hd] at hdd hdn hpd hpd' hsub ⊢
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = inner ℝ y d := ⟨_, rfl⟩
  rw [← hU]
  -- the midpoint of the pair
  obtain ⟨m, hm⟩ : ∃ m : V, m = (2 : ℝ)⁻¹ • (p + p') := ⟨_, rfl⟩
  have hmd : inner ℝ m d = 0 := by
    rw [hm, real_inner_smul_left, inner_add_left, hpd, hpd']
    ring
  have hmm : inner ℝ m m = 1 - r ^ 2 := by
    rw [hm, real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hp, hp', real_inner_comm p p', hr2]
    ring
  have hrd : r • d = (2 : ℝ)⁻¹ • (p - p') := by
    rw [hsub, smul_smul]
    congr 1
    ring
  have hpm : p = m + r • d := by
    rw [hm, hrd, ← smul_add]
    have : p + p' + (p - p') = (2 : ℝ) • p := by
      rw [two_smul]
      abel
    rw [this, smul_smul]
    norm_num
  have hpm' : p' = m - r • d := by
    rw [hm, hrd, ← smul_sub]
    have : p + p' - (p - p') = (2 : ℝ) • p' := by
      rw [two_smul]
      abel
    rw [this, smul_smul]
    norm_num
  have e1 : inner ℝ p y = inner ℝ m y + r * U := by
    conv_lhs => rw [hpm]
    rw [inner_add_left, real_inner_smul_left, real_inner_comm y d, hU]
  have e2 : inner ℝ p' y = inner ℝ m y - r * U := by
    conv_lhs => rw [hpm']
    rw [inner_sub_left, real_inner_smul_left, real_inner_comm y d, hU]
  -- the part of `y` orthogonal to `d`
  have hU1 : U ^ 2 ≤ 1 := by
    have h := abs_real_inner_le_norm y d
    rw [hy, hdn, mul_one, ← hU] at h
    have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    simpa using this
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = √(1 - U ^ 2) := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact Real.sqrt_nonneg _
  have hW2 : W ^ 2 = 1 - U ^ 2 := by
    rw [hW]
    exact Real.sq_sqrt (by linarith)
  have hrle : r ^ 2 ≤ 1 := by
    have := real_inner_self_nonneg (x := m)
    linarith
  obtain ⟨mn, hmn⟩ : ∃ mn : ℝ, mn = √(1 - r ^ 2) := ⟨_, rfl⟩
  have hmn0 : 0 ≤ mn := by
    rw [hmn]
    exact Real.sqrt_nonneg _
  have hmn2 : mn ^ 2 = 1 - r ^ 2 := by
    rw [hmn]
    exact Real.sq_sqrt (by linarith)
  have hcs : -(mn * W) ≤ inner ℝ m y := by
    have h3 : inner ℝ m y = inner ℝ m (y - U • d) := by
      rw [inner_sub_right, real_inner_smul_right, hmd, mul_zero, sub_zero]
    have h4 : ‖y - U • d‖ ^ 2 = 1 - U ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, real_inner_smul_right, real_inner_smul_left, hdd, real_inner_self_eq_norm_sq, hy,
        real_inner_comm y d, ← hU]
      ring
    have h5 : ‖m‖ ^ 2 = 1 - r ^ 2 := by rw [← real_inner_self_eq_norm_sq, hmm]
    have h6 : ‖m‖ = mn := by
      rw [hmn, ← h5, Real.sqrt_sq (norm_nonneg _)]
    have h7 : ‖y - U • d‖ = W := by
      rw [hW, ← h4, Real.sqrt_sq (norm_nonneg _)]
    have h8 := abs_real_inner_le_norm m (y - U • d)
    rw [h6, h7] at h8
    rw [h3]
    exact (abs_le.1 h8).1
  -- the two signs of `U`
  have hm₀ : mn ≤ √η := by
    rw [hmn]
    exact Real.sqrt_le_sqrt hη
  have hη0 : 0 ≤ η := by
    have := real_inner_self_nonneg (x := m)
    linarith
  have hs1 : √(1 - η) ^ 2 + √η ^ 2 = 1 := by
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt hη0]
    ring
  have hs2 : √η ^ 2 + T ^ 2 ≤ 1 := by
    rw [Real.sq_sqrt hη0]
    exact hηT
  have hb0 : 0 ≤ √(1 - η) * T + √η * √(1 - T ^ 2) :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hT) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have key : ∀ U' : ℝ, 0 ≤ U' → U' ^ 2 = U ^ 2 → r * U' - mn * W ≤ T →
      U' ≤ √(1 - η) * T + √η * √(1 - T ^ 2) := fun U' hU' hsq hle =>
    cap_core hmn0 hm₀ hr0 (by rw [hmn2]; ring) (Real.sqrt_nonneg _) hs1 hT hs2 hU' hW0
      (by rw [hsq, hW2]; ring) hle
  rw [abs_le]
  constructor
  · by_cases hneg : 0 ≤ -U
    · have := key (-U) hneg (by ring) (by linarith)
      linarith
    · rw [not_le] at hneg
      linarith
  · by_cases hpos : 0 ≤ U
    · exact key U hpos rfl (by linarith)
    · rw [not_le] at hpos
      linarith

/-! ## The Gram–Schmidt frame -/

/-- The second vector of the Gram–Schmidt frame of `e` and `eB`. -/
noncomputable def frameF (e eB : V) : V := (√(1 - inner ℝ e eB ^ 2))⁻¹ • (eB - inner ℝ e eB • e)

section Frame

variable {e eB : V} (he : ‖e‖ = 1) (heB : ‖eB‖ = 1) (hs : inner ℝ e eB ^ 2 < 1)

include hs in
theorem frame_c_pos : 0 < √(1 - inner ℝ e eB ^ 2) := Real.sqrt_pos.2 (by linarith)

include hs in
theorem frame_c_sq : √(1 - inner ℝ e eB ^ 2) ^ 2 = 1 - inner ℝ e eB ^ 2 := Real.sq_sqrt (by linarith)

include he hs in
theorem frame_orth : inner ℝ e (frameF e eB) = 0 := by
  unfold frameF
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

include hs in
/-- `eB = s • e + c • f`. -/
theorem frame_eB : eB = inner ℝ e eB • e + √(1 - inner ℝ e eB ^ 2) • frameF e eB := by
  have hc := frame_c_pos hs
  unfold frameF
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  abel

include he heB hs in
theorem frame_inner_self : inner ℝ (frameF e eB) (frameF e eB) = 1 := by
  have hc := frame_c_pos hs
  have hc2 := frame_c_sq hs
  have h1 : inner ℝ (eB - inner ℝ e eB • e) (eB - inner ℝ e eB • e) = 1 - inner ℝ e eB ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_smul_right, real_inner_smul_left, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, he, heB,
      real_inner_comm eB e]
    ring
  unfold frameF
  rw [real_inner_smul_left, real_inner_smul_right, h1]
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = √(1 - inner ℝ e eB ^ 2) := ⟨_, rfl⟩
  rw [← hcd] at hc hc2 ⊢
  rw [← hc2]
  field_simp

include he heB hs in
theorem frame_unit : ‖frameF e eB‖ = 1 := by
  have h := frame_inner_self he heB hs
  rw [real_inner_self_eq_norm_sq] at h
  have h0 : 0 ≤ ‖frameF e eB‖ := norm_nonneg _
  nlinarith

include hs in
/-- The inner product of a vector with `eB` in the frame. -/
theorem inner_eB (x : V) :
    inner ℝ x eB = inner ℝ e eB * inner ℝ x e + √(1 - inner ℝ e eB ^ 2) * inner ℝ x (frameF e eB) := by
  conv_lhs => rw [frame_eB (e := e) (eB := eB) hs]
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]

end Frame

/-! ## An orthonormal pair -/

section Orthonormal

variable {e f : V} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : inner ℝ e f = 0)

include he hf hef in
/-- The inner product of the parts of two vectors orthogonal to `e` and `f`. -/
theorem zeta_inner (x x' : V) :
    inner ℝ (x - inner ℝ x e • e - inner ℝ x f • f) (x' - inner ℝ x' e • e - inner ℝ x' f • f)
      = inner ℝ x x' - inner ℝ x e * inner ℝ x' e - inner ℝ x f * inner ℝ x' f := by
  have hfe : inner ℝ f e = 0 := by rw [real_inner_comm, hef]
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  have hff : inner ℝ f f = 1 := by rw [real_inner_self_eq_norm_sq, hf, one_pow]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hef, hfe, hee, hff,
    real_inner_comm e x, real_inner_comm f x, real_inner_comm e x', real_inner_comm f x']
  ring

include he hf hef in
/-- Bessel's inequality for an orthonormal pair. -/
theorem bessel2 {x : V} (hx : ‖x‖ = 1) : inner ℝ x e ^ 2 + inner ℝ x f ^ 2 ≤ 1 := by
  have h := zeta_inner he hf hef x x
  have h0 := real_inner_self_nonneg (x := x - inner ℝ x e • e - inner ℝ x f • f)
  rw [h, real_inner_self_eq_norm_sq, hx] at h0
  nlinarith

include he hf hef in
/-- The Cauchy–Schwarz inequality for the parts orthogonal to the frame: `H ^ 2 ≤ R R'`. -/
theorem zeta_cs {x x' : V} (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1) :
    (inner ℝ x x' - inner ℝ x e * inner ℝ x' e - inner ℝ x f * inner ℝ x' f) ^ 2
      ≤ (1 - inner ℝ x e ^ 2 - inner ℝ x f ^ 2) * (1 - inner ℝ x' e ^ 2 - inner ℝ x' f ^ 2) := by
  set z := x - inner ℝ x e • e - inner ℝ x f • f with hz
  set z' := x' - inner ℝ x' e • e - inner ℝ x' f • f with hz'
  have h1 : inner ℝ z z' = inner ℝ x x' - inner ℝ x e * inner ℝ x' e - inner ℝ x f * inner ℝ x' f :=
    zeta_inner he hf hef x x'
  have h2 : ‖z‖ ^ 2 = 1 - inner ℝ x e ^ 2 - inner ℝ x f ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hz, zeta_inner he hf hef x x, real_inner_self_eq_norm_sq, hx]
    ring
  have h3 : ‖z'‖ ^ 2 = 1 - inner ℝ x' e ^ 2 - inner ℝ x' f ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hz', zeta_inner he hf hef x' x', real_inner_self_eq_norm_sq, hx']
    ring
  have h4 := abs_real_inner_le_norm z z'
  have h5 : inner ℝ z z' ^ 2 ≤ (‖z‖ * ‖z'‖) ^ 2 := by
    have := sq_le_sq' (abs_le.1 h4).1 (abs_le.1 h4).2
    simpa using this
  rw [← h1, ← h2, ← h3]
  calc inner ℝ z z' ^ 2 ≤ (‖z‖ * ‖z'‖) ^ 2 := h5
    _ = ‖z‖ ^ 2 * ‖z'‖ ^ 2 := by ring

end Orthonormal

end S3N9
