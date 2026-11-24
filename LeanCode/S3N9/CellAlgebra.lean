module

public import S3N9.GramSchmidtCells
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The theorem for nine points: the algebra of the Gram–Schmidt cell lemma

The cell lemma of the source (`lma:gscell`) bounds the coordinates of the points of a labelled configuration in
its Gram–Schmidt frame by the constants of a cell. The source argues with angles. Here the bounds are derived
from the conditions (C1) to (C5) (`GSCell.Valid`) by algebra:

* `cstar_sq_add`: `c*² + s*² = 1`;
* `pairA_alg`: the pair `A`, from `u_a = r_A` and Bessel's inequality;
* `pairB_alg`: the pair `B`, from `s u + c v = r_B` and Bessel's inequality: with `ν = c u - s v` we have
  `r_B² + ν² = u² + v²` and `v = c r_B - s ν ≥ c*`, hence `u² ≤ 1 - v² ≤ s*²`;
* `ring_alg`: the ring points, from the bound `𝓗` for the coordinates along the two pairs;
* `dev_alg`: the deviations.

This is part of row A7 of `S3N9/README.md`.
-/

@[expose] public section

namespace S3N9

theorem abs_le_of_sq_le {x B : ℝ} (hB : 0 ≤ B) (h : x ^ 2 ≤ B ^ 2) : |x| ≤ B := by
  have := sq_le_sq.1 h
  rwa [abs_of_nonneg hB] at this

theorem sq_le_of_abs_le {x B : ℝ} (h : |x| ≤ B) : x ^ 2 ≤ B ^ 2 :=
  sq_le_sq' (neg_le_of_abs_le h) (le_of_abs_le h)

theorem le_one_of_sq_le_one {x : ℝ} (h : x ^ 2 ≤ 1) : x ≤ 1 :=
  le_trans (le_abs_self x) (abs_le_of_sq_le zero_le_one (by rw [one_pow]; exact h))

theorem abs_mul_le_of {ε a b A B : ℝ} (hε : |ε| = 1) (ha : |a| ≤ A) (hb : |b| ≤ B) : |ε * (a * b)| ≤ A * B := by
  rw [abs_mul, hε, one_mul, abs_mul]
  exact mul_le_mul ha hb (abs_nonneg b) (le_trans (abs_nonneg a) ha)

/-- A deviation `H - X - Y` with three bounded terms. -/
theorem dev_alg {H X Y B0 B1 B2 σ : ℝ} (h0 : |H| ≤ B0) (h1 : |X| ≤ B1) (h2 : |Y| ≤ B2) (hσ : B0 + B1 + B2 ≤ σ) :
    (H - X - Y) ^ 2 ≤ σ ^ 2 := by
  have a0 := abs_le.1 h0
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  exact sq_le_sq' (by linarith) (by linarith)

namespace GSCell

/-- The signs of the constants of a cell that the cell lemma uses, and the equality of the two caps. -/
structure Pos (C : GSCell) : Prop where
  cA0 : 0 < C.cA
  cA1 : C.cA ≤ 1
  cAB : C.cA = C.cB
  σ0 : 0 ≤ C.σ
  T0 : 0 ≤ C.T
  εR0 : 0 ≤ C.εR

variable {C : GSCell}

theorem ηA_nonneg (hP : C.Pos) : 0 ≤ C.ηA := by
  unfold ηA
  linarith [hP.cA1]

theorem ηB_eq (hP : C.Pos) : C.ηB = C.ηA := by
  unfold ηA ηB
  rw [hP.cAB]

theorem ηB_nonneg (hP : C.Pos) : 0 ≤ C.ηB := by
  rw [ηB_eq hP]
  exact ηA_nonneg hP

theorem σ_sq_lt (hC : C.Valid) (hP : C.Pos) : C.σ ^ 2 < 1 := by
  have := hC.c1b
  have := ηB_nonneg hP
  linarith

theorem ηB_lt (hC : C.Valid) : C.ηB < 1 := by
  have := hC.c1b
  nlinarith [sq_nonneg C.σ]

theorem cstar_eq (hC : C.Valid) (hP : C.Pos) : C.cstar = √(1 - C.σ ^ 2) * √(1 - C.ηB) - C.σ * √C.ηB := by
  unfold cstar
  rw [Real.sqrt_mul (by linarith [σ_sq_lt hC hP])]

theorem sstar_eq (hC : C.Valid) (hP : C.Pos) : C.sstar = C.σ * √(1 - C.ηB) + √(1 - C.σ ^ 2) * √C.ηB := by
  unfold sstar
  rw [Real.sqrt_mul (by linarith [σ_sq_lt hC hP])]

/-- `cos² + sin² = 1` for the angle `ϑmax + φB`. -/
theorem cstar_sq_add (hC : C.Valid) (hP : C.Pos) : C.cstar ^ 2 + C.sstar ^ 2 = 1 := by
  rw [cstar_eq hC hP, sstar_eq hC hP]
  have h1 : √(1 - C.σ ^ 2) ^ 2 = 1 - C.σ ^ 2 := Real.sq_sqrt (by linarith [σ_sq_lt hC hP])
  have h2 : √(1 - C.ηB) ^ 2 = 1 - C.ηB := Real.sq_sqrt (by linarith [ηB_lt hC])
  have h3 : √C.ηB ^ 2 = C.ηB := Real.sq_sqrt (ηB_nonneg hP)
  have e : ∀ p q n σ : ℝ, (p * q - σ * n) ^ 2 + (σ * q + p * n) ^ 2 = (p ^ 2 + σ ^ 2) * (q ^ 2 + n ^ 2) := by
    intros
    ring
  rw [e, h1, h2, h3]
  ring

theorem cstar_pos (hC : C.Valid) (hP : C.Pos) : 0 < C.cstar := by
  rw [cstar_eq hC hP]
  have h1 : √(1 - C.σ ^ 2) ^ 2 = 1 - C.σ ^ 2 := Real.sq_sqrt (by linarith [σ_sq_lt hC hP])
  have h2 : √(1 - C.ηB) ^ 2 = 1 - C.ηB := Real.sq_sqrt (by linarith [ηB_lt hC])
  have h3 : √C.ηB ^ 2 = C.ηB := Real.sq_sqrt (ηB_nonneg hP)
  have hp := Real.sqrt_nonneg (1 - C.σ ^ 2)
  have hq := Real.sqrt_nonneg (1 - C.ηB)
  have hn := Real.sqrt_nonneg C.ηB
  have hlt : (C.σ * √C.ηB) ^ 2 < (√(1 - C.σ ^ 2) * √(1 - C.ηB)) ^ 2 := by
    rw [mul_pow, mul_pow, h1, h2, h3]
    nlinarith [hC.c1b]
  have h := sq_lt_sq.1 hlt
  rw [abs_of_nonneg (mul_nonneg hP.σ0 hn), abs_of_nonneg (mul_nonneg hp hq)] at h
  linarith

theorem sstar_nonneg (hC : C.Valid) (hP : C.Pos) : 0 ≤ C.sstar := by
  rw [sstar_eq hC hP]
  exact add_nonneg (mul_nonneg hP.σ0 (Real.sqrt_nonneg _)) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- **The pair `A`** (`lma:gscell` (i)): `rA` is the coordinate `ε u` of a point of the pair along `e`, and `N`
its coordinate along `f`. -/
theorem pairA_alg (hC : C.Valid) (hP : C.Pos) {rA N : ℝ} (hrA : 1 - C.ηA ≤ rA ^ 2) (hrA0 : 0 < rA)
    (hbes : rA ^ 2 + N ^ 2 ≤ 1) :
    0 ≤ 1 - rA ∧ 1 - rA ≤ C.εAP ∧ N ^ 2 ≤ C.εAQ ^ 2 ∧ 1 - rA ^ 2 - N ^ 2 ≤ C.ηA
      ∧ N ^ 2 ≤ C.κA ^ 2 * rA ^ 2 ∧ N ^ 2 ≤ C.ηA := by
  have hη0 := ηA_nonneg hP
  have hr1 : rA ≤ 1 := by nlinarith [sq_nonneg N]
  have hq : √(1 - C.ηA) ≤ rA := by
    have h1 := Real.sqrt_le_sqrt hrA
    rwa [Real.sqrt_sq (le_of_lt hrA0)] at h1
  have hN : N ^ 2 ≤ C.ηA := by linarith
  refine ⟨by linarith, by linarith [hC.c2a], ?_, by linarith [sq_nonneg N], ?_, hN⟩
  · have h1 : √C.ηA ^ 2 = C.ηA := Real.sq_sqrt hη0
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg C.ηA) hC.c2c 2
    linarith
  · have h1 : C.κA ^ 2 * (1 - C.ηA) ≤ C.κA ^ 2 * rA ^ 2 := mul_le_mul_of_nonneg_left hrA (sq_nonneg _)
    linarith [hC.c2d]

/-- **The pair `B`** (`lma:gscell` (ii)): `M = ε v` and `N = u` are the coordinates of a point of the pair, with
`s N + c M = r_B` for the tilt `s` (multiplied by the sign of the point). -/
theorem pairB_alg (hC : C.Valid) (hP : C.Pos) {s c rB M N : ℝ} (hs : |s| ≤ C.σ) (hc : 0 < c)
    (hsc : s ^ 2 + c ^ 2 = 1) (hrB : 1 - C.ηB ≤ rB ^ 2) (hrB0 : 0 < rB) (hrel : s * N + c * M = rB)
    (hbes : M ^ 2 + N ^ 2 ≤ 1) :
    C.cstar ≤ M ∧ M ≤ 1 ∧ 1 - M ≤ C.εBP ∧ N ^ 2 ≤ C.εBQ ^ 2 ∧ 1 - M ^ 2 - N ^ 2 ≤ C.ηB
      ∧ N ^ 2 ≤ C.κB ^ 2 * M ^ 2
      ∧ N ^ 2 ≤ 12 / 5 * C.σ ^ 2 + 12 / 7 * (C.ηB - (1 - M ^ 2 - N ^ 2)) := by
  have hσ0 := hP.σ0
  have hη0 := ηB_nonneg hP
  have hσ1 := σ_sq_lt hC hP
  have hη1 := ηB_lt hC
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = c * N - s * M := ⟨_, rfl⟩
  have e1 : rB ^ 2 + ν ^ 2 = M ^ 2 + N ^ 2 := by
    have : rB ^ 2 + ν ^ 2 = (s ^ 2 + c ^ 2) * (M ^ 2 + N ^ 2) := by
      rw [← hrel, hν]
      ring
    rw [this, hsc, one_mul]
  have e2 : M = c * rB - s * ν := by
    have : c * rB - s * ν = (s ^ 2 + c ^ 2) * M := by
      rw [← hrel, hν]
      ring
    rw [this, hsc, one_mul]
  have e3 : N = s * rB + c * ν := by
    have : s * rB + c * ν = (s ^ 2 + c ^ 2) * N := by
      rw [← hrel, hν]
      ring
    rw [this, hsc, one_mul]
  have hs2 : s ^ 2 ≤ C.σ ^ 2 := sq_le_of_abs_le hs
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = √(1 - C.σ ^ 2) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = √(1 - C.ηB) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = √C.ηB := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := by
    rw [hp]
    exact Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := by
    rw [hq]
    exact Real.sqrt_nonneg _
  have hn0 : 0 ≤ n := by
    rw [hn]
    exact Real.sqrt_nonneg _
  have hp2 : p ^ 2 = 1 - C.σ ^ 2 := by
    rw [hp]
    exact Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = 1 - C.ηB := by
    rw [hq]
    exact Real.sq_sqrt (by linarith)
  have hn2 : n ^ 2 = C.ηB := by
    rw [hn]
    exact Real.sq_sqrt hη0
  have hcs : C.cstar = p * q - C.σ * n := by rw [cstar_eq hC hP, ← hp, ← hq, ← hn]
  have hpc : p ≤ c := by
    have h1 : p ^ 2 ≤ c ^ 2 := by
      rw [hp2]
      linarith
    have h2 := sq_le_sq.1 h1
    rwa [abs_of_nonneg hp0, abs_of_nonneg (le_of_lt hc)] at h2
  have hqr : q ≤ rB := by
    have h1 : q ^ 2 ≤ rB ^ 2 := by
      rw [hq2]
      exact hrB
    have h2 := sq_le_sq.1 h1
    rwa [abs_of_nonneg hq0, abs_of_nonneg (le_of_lt hrB0)] at h2
  have hνn : |ν| ≤ n := abs_le_of_sq_le hn0 (by rw [hn2]; linarith)
  have hM : C.cstar ≤ M := by
    rw [hcs, e2]
    have h1 : p * q ≤ c * rB := mul_le_mul hpc hqr hq0 (le_of_lt hc)
    have h2 : s * ν ≤ C.σ * n :=
      calc s * ν ≤ |s * ν| := le_abs_self _
        _ = |s| * |ν| := abs_mul s ν
        _ ≤ C.σ * n := mul_le_mul hs hνn (abs_nonneg ν) hσ0
    linarith
  have hcs0 := cstar_pos hC hP
  have hss0 := sstar_nonneg hC hP
  have hid := cstar_sq_add hC hP
  have hM1 : M ≤ 1 := le_one_of_sq_le_one (by linarith [sq_nonneg N])
  have hM2 : C.cstar ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (le_of_lt hcs0) hM 2
  have hN2 : N ^ 2 ≤ C.sstar ^ 2 := by linarith
  refine ⟨hM, hM1, by linarith [hC.c3a], ?_, by nlinarith [sq_nonneg ν], ?_, ?_⟩
  · have := pow_le_pow_left₀ hss0 hC.c3b 2
    linarith
  · have h1 := pow_le_pow_left₀ hss0 hC.c3c 2
    have h2 : (C.κB * C.cstar) ^ 2 ≤ C.κB ^ 2 * M ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hM2 (sq_nonneg _)
    linarith
  · have hrB1 : rB ≤ 1 := le_one_of_sq_le_one (by linarith [sq_nonneg ν])
    have hc1 : c ≤ 1 := le_one_of_sq_le_one (by linarith [sq_nonneg s])
    have hNabs : |N| ≤ C.σ + |ν| := by
      rw [e3]
      calc |s * rB + c * ν| ≤ |s * rB| + |c * ν| := abs_add_le _ _
        _ = |s| * rB + c * |ν| := by rw [abs_mul, abs_mul, abs_of_pos hrB0, abs_of_pos hc]
        _ ≤ C.σ * 1 + 1 * |ν| :=
          add_le_add (mul_le_mul hs hrB1 (le_of_lt hrB0) hσ0) (mul_le_mul_of_nonneg_right hc1 (abs_nonneg ν))
        _ = C.σ + |ν| := by ring
    have hN2' : N ^ 2 ≤ (C.σ + |ν|) ^ 2 := sq_le_of_abs_le hNabs
    have hν2 : |ν| ^ 2 = ν ^ 2 := sq_abs ν
    have hνle : ν ^ 2 ≤ C.ηB - (1 - M ^ 2 - N ^ 2) := by linarith
    have h7 := sq_nonneg (7 * C.σ - 5 * |ν|)
    have e7 : (7 * C.σ - 5 * |ν|) ^ 2 = 49 * C.σ ^ 2 - 70 * (C.σ * |ν|) + 25 * ν ^ 2 := by
      rw [← hν2]
      ring
    have e8 : (C.σ + |ν|) ^ 2 = C.σ ^ 2 + 2 * (C.σ * |ν|) + ν ^ 2 := by
      rw [← hν2]
      ring
    rw [e8] at hN2'
    rw [e7] at h7
    linarith

/-- **The ring points** (`lma:gscell` (iii)): `u`, `v` are the coordinates of a ring point in the frame and
`w = s u + c v` its coordinate along the pair `B`. -/
theorem ring_alg (hC : C.Valid) (hP : C.Pos) {s c u v w : ℝ} (hs : |s| ≤ C.σ) (hc : 0 < c)
    (hsc : s ^ 2 + c ^ 2 = 1) (hw : w = s * u + c * v) (hu : |u| ≤ C.hcap C.cA) (hwb : |w| ≤ C.hcap C.cA) :
    u ^ 2 ≤ C.εR ^ 2 ∧ v ^ 2 ≤ C.εR ^ 2 := by
  have hσ0 := hP.σ0
  have hσ1 := σ_sq_lt hC hP
  have h4 := hC.c4a
  rw [← hP.cAB, min_self] at h4
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = C.hcap C.cA := ⟨_, rfl⟩
  rw [← hh] at hu hwb h4
  have hh0 : 0 ≤ h := le_trans (abs_nonneg u) hu
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = √(1 - C.σ ^ 2) := ⟨_, rfl⟩
  rw [← hp] at h4
  have hp0 : 0 ≤ p := by
    rw [hp]
    exact Real.sqrt_nonneg _
  have hp2 : p ^ 2 = 1 - C.σ ^ 2 := by
    rw [hp]
    exact Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 ≤ C.σ ^ 2 := sq_le_of_abs_le hs
  have hpc : p ≤ c := by
    have h1 : p ^ 2 ≤ c ^ 2 := by
      rw [hp2]
      linarith
    have h2 := sq_le_sq.1 h1
    rwa [abs_of_nonneg hp0, abs_of_nonneg (le_of_lt hc)] at h2
  have hp1 : p ≤ 1 := le_one_of_sq_le_one (by linarith [sq_nonneg C.σ])
  have hε := hP.εR0
  have hεp : C.εR * p ≤ C.εR := by
    have := mul_le_mul_of_nonneg_left hp1 hε
    linarith
  have hσh : 0 ≤ C.σ * h := mul_nonneg hσ0 hh0
  constructor
  · exact sq_le_of_abs_le (by linarith)
  · have h1 : c * |v| ≤ C.εR * c := by
      have e : c * v = w - s * u := by
        rw [hw]
        ring
      have h2 : |c * v| ≤ h + C.σ * h := by
        rw [e]
        calc |w - s * u| ≤ |w| + |s * u| := abs_sub _ _
          _ = |w| + |s| * |u| := by rw [abs_mul]
          _ ≤ h + C.σ * h := add_le_add hwb (mul_le_mul hs hu (abs_nonneg u) hσ0)
      rw [abs_mul, abs_of_pos hc] at h2
      have h3 : C.εR * p ≤ C.εR * c := mul_le_mul_of_nonneg_left hpc hε
      linarith
    have h2 : |v| ≤ C.εR := by
      have h5 : c * |v| ≤ c * C.εR := by linarith
      exact le_of_mul_le_mul_left h5 hc
    exact sq_le_of_abs_le h2

/-! ## The facts of the cell lemma for the three kinds of points -/

/-- The facts of the cell lemma for a point of the pair `A` with the sign `ε`, in its coordinates `u`, `v`. -/
structure APt (C : GSCell) (ε u v : ℝ) : Prop where
  sgn : |ε| = 1
  p0 : 0 ≤ 1 - ε * u
  p1 : 1 - ε * u ≤ C.εAP
  q : v ^ 2 ≤ C.εAQ ^ 2
  r0 : 0 ≤ 1 - u ^ 2 - v ^ 2
  r1 : 1 - u ^ 2 - v ^ 2 ≤ C.ηA
  cone : v ^ 2 ≤ C.κA ^ 2 * (ε * u) ^ 2
  gs : 1 - u ^ 2 ≤ C.ηA

/-- The facts of the cell lemma for a point of the pair `B` with the sign `ε`. -/
structure BPt (C : GSCell) (ε u v : ℝ) : Prop where
  sgn : |ε| = 1
  p0 : 0 ≤ 1 - ε * v
  p1 : 1 - ε * v ≤ C.εBP
  q : u ^ 2 ≤ C.εBQ ^ 2
  r0 : 0 ≤ 1 - u ^ 2 - v ^ 2
  r1 : 1 - u ^ 2 - v ^ 2 ≤ C.ηB
  cone : u ^ 2 ≤ C.κB ^ 2 * (ε * v) ^ 2
  gs : u ^ 2 ≤ 12 / 5 * C.σ ^ 2 + 12 / 7 * (C.ηB - (1 - u ^ 2 - v ^ 2))

/-- The facts of the cell lemma for a ring point. -/
structure RPt (C : GSCell) (u v : ℝ) : Prop where
  u2 : u ^ 2 ≤ C.εR ^ 2
  v2 : v ^ 2 ≤ C.εR ^ 2
  r0 : 0 ≤ 1 - u ^ 2 - v ^ 2

theorem sq_of_abs_one {ε : ℝ} (h : |ε| = 1) : ε ^ 2 = 1 := by
  rw [← sq_abs, h, one_pow]

theorem aPt_of (hC : C.Valid) (hP : C.Pos) {ε u v rA : ℝ} (hε : |ε| = 1) (hu : ε * u = rA)
    (hrA : 1 - C.ηA ≤ rA ^ 2) (hrA0 : 0 < rA) (hbes : u ^ 2 + v ^ 2 ≤ 1) : APt C ε u v := by
  have h2 := sq_of_abs_one hε
  have e : u ^ 2 = rA ^ 2 := by
    rw [← hu, mul_pow, h2, one_mul]
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := pairA_alg hC hP (N := v) hrA hrA0 (by rw [← e]; exact hbes)
  exact ⟨hε, by rw [hu]; exact a1, by rw [hu]; exact a2, a3, by linarith, by rw [e]; exact a4,
    by rw [hu]; exact a5, by rw [e]; linarith⟩

theorem bPt_of (hC : C.Valid) (hP : C.Pos) {ε s c u v rB : ℝ} (hε : |ε| = 1) (hs : |s| ≤ C.σ) (hc : 0 < c)
    (hsc : s ^ 2 + c ^ 2 = 1) (hrB : 1 - C.ηB ≤ rB ^ 2) (hrB0 : 0 < rB) (hrel : s * u + c * v = ε * rB)
    (hbes : u ^ 2 + v ^ 2 ≤ 1) : BPt C ε u v := by
  have h2 := sq_of_abs_one hε
  have e : (ε * v) ^ 2 = v ^ 2 := by rw [mul_pow, h2, one_mul]
  have hrel' : ε * s * u + c * (ε * v) = rB := by
    have : ε * s * u + c * (ε * v) = ε * (s * u + c * v) := by ring
    rw [this, hrel, ← mul_assoc, ← sq, h2, one_mul]
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := pairB_alg hC hP (s := ε * s) (c := c) (rB := rB) (M := ε * v) (N := u)
    (by rw [abs_mul, hε, one_mul]; exact hs) hc (by rw [mul_pow, h2, one_mul]; exact hsc) hrB hrB0 hrel'
    (by rw [e]; linarith)
  rw [e] at b5 b7
  exact ⟨hε, by linarith, b3, b4, by linarith, by linarith, b6, by linarith⟩

theorem εAQ_nonneg (hC : C.Valid) : 0 ≤ C.εAQ := le_trans (Real.sqrt_nonneg _) hC.c2c

theorem εBQ_nonneg (hC : C.Valid) (hP : C.Pos) : 0 ≤ C.εBQ := le_trans (sstar_nonneg hC hP) hC.c3b

/-- **The deviation between a point of `A` and a point of `B`** (`lma:gscell` (iv)). -/
theorem devAB (hC : C.Valid) (hP : C.Pos) {εa ua va εb ub vb t : ℝ} (ha : APt C εa ua va) (hb : BPt C εb ub vb)
    (hH : (t - ua * ub - va * vb) ^ 2 ≤ (1 - ua ^ 2 - va ^ 2) * (1 - ub ^ 2 - vb ^ 2)) :
    (t - εb * va - εa * ub) ^ 2 ≤ C.σAB ^ 2 := by
  have hεa2 := sq_of_abs_one ha.sgn
  have hεb2 := sq_of_abs_one hb.sgn
  have e : t - εb * va - εa * ub
      = (t - ua * ub - va * vb) - εa * ((1 - εa * ua) * ub) - εb * ((1 - εb * vb) * va) := by
    linear_combination (-(ua * ub)) * hεa2 + (-(va * vb)) * hεb2
  rw [e]
  have h0 : |t - ua * ub - va * vb| ≤ √(C.ηA * C.ηB) :=
    Real.abs_le_sqrt (le_trans hH (mul_le_mul ha.r1 hb.r1 hb.r0 (ηA_nonneg hP)))
  have h1 : |εa * ((1 - εa * ua) * ub)| ≤ C.εAP * C.εBQ :=
    abs_mul_le_of ha.sgn (by rw [abs_of_nonneg ha.p0]; exact ha.p1) (abs_le_of_sq_le (εBQ_nonneg hC hP) hb.q)
  have h2 : |εb * ((1 - εb * vb) * va)| ≤ C.εBP * C.εAQ :=
    abs_mul_le_of hb.sgn (by rw [abs_of_nonneg hb.p0]; exact hb.p1) (abs_le_of_sq_le (εAQ_nonneg hC) ha.q)
  exact dev_alg h0 h1 h2 hC.c5a

/-- **The deviation between a point of `A` and a ring point.** -/
theorem devAR (hC : C.Valid) (hP : C.Pos) {εa ua va u v t : ℝ} (ha : APt C εa ua va) (hr : RPt C u v)
    (hH : (t - ua * u - va * v) ^ 2 ≤ (1 - ua ^ 2 - va ^ 2) * (1 - u ^ 2 - v ^ 2)) :
    (t - εa * u) ^ 2 ≤ C.σAR ^ 2 := by
  have hεa2 := sq_of_abs_one ha.sgn
  have e : t - εa * u = (t - ua * u - va * v) - εa * ((1 - εa * ua) * u) - (-1) * (va * v) := by
    linear_combination (-(ua * u)) * hεa2
  rw [e]
  have hr1 : 1 - u ^ 2 - v ^ 2 ≤ 1 := by linarith [sq_nonneg u, sq_nonneg v]
  have h0 : |t - ua * u - va * v| ≤ √C.ηA := by
    refine Real.abs_le_sqrt (le_trans hH ?_)
    have := mul_le_mul ha.r1 hr1 hr.r0 (ηA_nonneg hP)
    linarith
  have h1 : |εa * ((1 - εa * ua) * u)| ≤ C.εAP * C.εR :=
    abs_mul_le_of ha.sgn (by rw [abs_of_nonneg ha.p0]; exact ha.p1) (abs_le_of_sq_le hP.εR0 hr.u2)
  have h2 : |(-1 : ℝ) * (va * v)| ≤ C.εAQ * C.εR :=
    abs_mul_le_of (by norm_num) (abs_le_of_sq_le (εAQ_nonneg hC) ha.q) (abs_le_of_sq_le hP.εR0 hr.v2)
  exact dev_alg h0 h1 h2 (by linarith [hC.c5b])

/-- **The deviation between a point of `B` and a ring point.** -/
theorem devBR (hC : C.Valid) (hP : C.Pos) {εb ub vb u v t : ℝ} (hb : BPt C εb ub vb) (hr : RPt C u v)
    (hH : (t - ub * u - vb * v) ^ 2 ≤ (1 - ub ^ 2 - vb ^ 2) * (1 - u ^ 2 - v ^ 2)) :
    (t - εb * v) ^ 2 ≤ C.σBR ^ 2 := by
  have hεb2 := sq_of_abs_one hb.sgn
  have e : t - εb * v = (t - ub * u - vb * v) - εb * ((1 - εb * vb) * v) - (-1) * (ub * u) := by
    linear_combination (-(vb * v)) * hεb2
  rw [e]
  have hr1 : 1 - u ^ 2 - v ^ 2 ≤ 1 := by linarith [sq_nonneg u, sq_nonneg v]
  have h0 : |t - ub * u - vb * v| ≤ √C.ηB := by
    refine Real.abs_le_sqrt (le_trans hH ?_)
    have := mul_le_mul hb.r1 hr1 hr.r0 (ηB_nonneg hP)
    linarith
  have h1 : |εb * ((1 - εb * vb) * v)| ≤ C.εBP * C.εR :=
    abs_mul_le_of hb.sgn (by rw [abs_of_nonneg hb.p0]; exact hb.p1) (abs_le_of_sq_le hP.εR0 hr.v2)
  have h2 : |(-1 : ℝ) * (ub * u)| ≤ C.εBQ * C.εR :=
    abs_mul_le_of (by norm_num) (abs_le_of_sq_le (εBQ_nonneg hC hP) hb.q) (abs_le_of_sq_le hP.εR0 hr.u2)
  exact dev_alg h0 h1 h2 (by linarith [hC.c5c])

/-- The bound for the coordinate of a ring point along a pair, in the form of `abs_inner_dir_le`. -/
theorem hcap_eq (hP : C.Pos) : C.hcap C.cA = √(1 - C.ηA) * C.T + √C.ηA * √(1 - C.T ^ 2) := by
  unfold hcap
  have e1 : (1 + C.cA) / 2 = 1 - C.ηA := by
    unfold ηA
    ring
  have e2 : (1 - C.cA) * (1 - C.T ^ 2) / 2 = C.ηA * (1 - C.T ^ 2) := by
    unfold ηA
    ring
  rw [e1, e2, Real.sqrt_mul (ηA_nonneg hP)]
  ring

end GSCell

end S3N9
