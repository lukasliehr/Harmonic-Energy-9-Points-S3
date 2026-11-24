module

public import Mathlib.Tactic.Linarith
public import CAP.VR.Config

/-!
# Virtual-root certificates: the inequality of a pair of labels

For a pair `i < j` of labels with the record type `h`, the structure `RecFacts` collects what the identity of
the record type needs at the data `y` of the pair: the coordinates of the two end points and their inner
product, as the checker forms them, are those of the two labels, up to common signs; the weights of the end
points are nonnegative; the blocks of the kernel, the exchange polynomials and the minorant are those of the
labels. From these facts and from the two checks (`recordOk`, `minoOk`) we obtain

  `C + 2 K(i, j) + π(i; j) + π(j; i) - (loss of the record) - (loss of the minorant) ≤ 1 / (2 - 2 t)`

(`pair_ineq`). The lemmas `endA`, `endB`, `endR` treat an end point of each of the three classes.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ}

/-! ## Small facts -/

theorem beq_false_of_ne {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem cast_mul_shl (a n : ℕ) : ((Nat.mul a (Nat.shiftLeft 1 n) : ℕ) : ℝ) = a * 2 ^ n := by
  rw [show Nat.mul a (Nat.shiftLeft 1 n) = a * Nat.shiftLeft 1 n from rfl, Nat.cast_mul, cast_shl1]

theorem mem_cond {α : Type} {b : Bool} {l1 l2 : List α} {g : α} (h : g ∈ cond b l1 l2) :
    (b = true ∧ g ∈ l1) ∨ (b = false ∧ g ∈ l2) := by
  cases b
  · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩

/-- The sign of an end point of a record type: `-1` for the second point of a pair. -/
noncomputable def sgA (sg : ℕ) : ℝ := if sg = 1 then -1 else 1

theorem sgA_sq (sg : ℕ) : sgA sg ^ 2 = 1 := by
  unfold sgA
  split_ifs <;> norm_num

theorem signed_real (sg : ℕ) (x : ℝ) : signed (realOps W L y) sg x = sgA sg * x := by
  unfold signed sgA
  by_cases h : sg = 1
  · rw [h, if_pos rfl]
    show ((0 : ℕ) : ℝ) - x = -1 * x
    simp
  · rw [beq_false_of_ne h, if_neg h]
    show x = 1 * x
    ring

/-- The second end point of a record type has the variables `i2p`, `i2q`. -/
abbrev i2p (h : RecH) : ℕ := cond (Nat.beq h.kind 0) 0 2

abbrev i2q (h : RecH) : ℕ := cond (Nat.beq h.kind 0) 1 3

/-! ## Gram determinants -/

theorem gram_nonneg {u v ξ η u' v' ξ' η' t : ℝ} (h : u ^ 2 + v ^ 2 + ξ ^ 2 + η ^ 2 = 1)
    (h' : u' ^ 2 + v' ^ 2 + ξ' ^ 2 + η' ^ 2 = 1) (ht : t = u * u' + v * v' + ξ * ξ' + η * η') :
    0 ≤ 1 + 2 * u * u' * t - u ^ 2 - u' ^ 2 - t ^ 2 := by
  have e : 1 + 2 * u * u' * t - u ^ 2 - u' ^ 2 - t ^ 2
      = (v * ξ' - ξ * v') ^ 2 + (v * η' - η * v') ^ 2 + (ξ * η' - η * ξ') ^ 2 := by
    rw [ht]
    linear_combination (-(1 - u' ^ 2)) * h - (v ^ 2 + ξ ^ 2 + η ^ 2) * h'
  rw [e]
  positivity

theorem gram2_nonneg (C : Conf) (i j : ℕ) : 0 ≤ C.R i * C.R j - C.Hh i j ^ 2 := by
  have e : C.R i * C.R j - C.Hh i j ^ 2 = (C.ξ i * C.η j - C.η i * C.ξ j) ^ 2 := by
    unfold Conf.R Conf.Hh
    ring
  rw [e]
  positivity

theorem t_eq (C : Conf) (i j : ℕ) : C.t i j = C.u i * C.u j + C.v i * C.v j + C.Hh i j := by
  unfold Conf.t Conf.Hh
  ring

/-! ## The geometry of a record at real points -/

theorem clsR_real (m : ℕ) {σu σv u v ξ η : ℝ} (hsu : σu ^ 2 = 1) (hsv : σv ^ 2 = 1)
    (hun : u ^ 2 + v ^ 2 + ξ ^ 2 + η ^ 2 = 1) :
    clsR (realOps W L y) m (2 ^ m * (σu * u)) (2 ^ m * (σv * v)) = 2 ^ (2 * m) * (ξ ^ 2 + η ^ 2) := by
  show ((Nat.shiftLeft 1 (Nat.mul 2 m) : ℕ) : ℝ)
    - ((2 ^ m * (σu * u)) * (2 ^ m * (σu * u)) + (2 ^ m * (σv * v)) * (2 ^ m * (σv * v))) = _
  rw [cast_shl1]
  show (2 : ℝ) ^ (2 * m) - _ = _
  have e : (2 : ℝ) ^ (2 * m) = 2 ^ m * 2 ^ m := by rw [two_mul, pow_add]
  rw [e]
  linear_combination (-(2 ^ m * 2 ^ m)) * hun - (2 ^ m * 2 ^ m * u ^ 2) * hsu - (2 ^ m * 2 ^ m * v ^ 2) * hsv

theorem recHv_real (m1 m2 mT : ℕ) {σu σv : ℝ} (hsu : σu ^ 2 = 1) (hsv : σv ^ 2 = 1) {ui vi uj vj t Hx : ℝ}
    (ht : t = ui * uj + vi * vj + Hx) :
    recHv (realOps W L y) m1 m2 mT (2 ^ m1 * (σu * ui)) (2 ^ m1 * (σv * vi)) (2 ^ m2 * (σu * uj)) (2 ^ m2 * (σv * vj))
        (2 ^ mT * t)
      = 2 ^ (mT + m1 + m2) * Hx := by
  show ((Nat.shiftLeft 1 (Nat.add m1 m2) : ℕ) : ℝ) * (2 ^ mT * t)
    - ((Nat.shiftLeft 1 mT : ℕ) : ℝ) * ((2 ^ m1 * (σu * ui)) * (2 ^ m2 * (σu * uj)) + (2 ^ m1 * (σv * vi)) * (2 ^ m2 * (σv * vj)))
    = _
  rw [cast_shl1, cast_shl1, ht]
  show (2 : ℝ) ^ (m1 + m2) * _ - _ = _
  rw [pow_add, pow_add, pow_add]
  linear_combination (-(2 ^ m1 * 2 ^ m2 * 2 ^ mT * (ui * uj))) * hsu - (2 ^ m1 * 2 ^ m2 * 2 ^ mT * (vi * vj)) * hsv

theorem locT_nonneg (h : RecH) (mT : ℕ) {t : ℝ} (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * t)
    (hhi : (h.hid : ℝ) * t ≤ (h.hip : ℝ) - h.hin) : 0 ≤ locT (realOps W L y) h (2 ^ mT * t) mT := by
  show 0 ≤ ((h.lod : ℝ) * (2 ^ mT * t) + ((Nat.mul h.lon (Nat.shiftLeft 1 mT) : ℕ) : ℝ)
      - ((Nat.mul h.lop (Nat.shiftLeft 1 mT) : ℕ) : ℝ))
    * (((Nat.mul h.hip (Nat.shiftLeft 1 mT) : ℕ) : ℝ)
      - ((h.hid : ℝ) * (2 ^ mT * t) + ((Nat.mul h.hin (Nat.shiftLeft 1 mT) : ℕ) : ℝ)))
  rw [cast_mul_shl, cast_mul_shl, cast_mul_shl, cast_mul_shl]
  have h2 : (0 : ℝ) ≤ 2 ^ mT := by positivity
  have e : ((h.lod : ℝ) * (2 ^ mT * t) + (h.lon : ℝ) * 2 ^ mT - (h.lop : ℝ) * 2 ^ mT)
      * ((h.hip : ℝ) * 2 ^ mT - ((h.hid : ℝ) * (2 ^ mT * t) + (h.hin : ℝ) * 2 ^ mT))
      = (2 ^ mT * ((h.lod : ℝ) * t - ((h.lop : ℝ) - h.lon))) * (2 ^ mT * ((h.hip : ℝ) - h.hin - h.hid * t)) := by ring
  rw [e]
  exact mul_nonneg (mul_nonneg h2 (by linarith)) (mul_nonneg h2 (by linarith))

theorem locG3_real (m1 m2 mT : ℕ) (a1 a2 t : ℝ) :
    locG3 (realOps W L y) (2 ^ m1 * a1) (2 ^ m2 * a2) (2 ^ mT * t) m1 m2 mT
      = (2 ^ (m1 + m2 + mT)) ^ 2 * (1 + 2 * a1 * a2 * t - a1 ^ 2 - a2 ^ 2 - t ^ 2) := by
  show ((Nat.shiftLeft 1 (Nat.mul 2 (Nat.add (Nat.add m1 m2) mT)) : ℕ) : ℝ)
      + ((Nat.shiftLeft 1 (Nat.succ (Nat.add (Nat.add m1 m2) mT)) : ℕ) : ℝ) * ((2 ^ m1 * a1) * (2 ^ m2 * a2) * (2 ^ mT * t))
    - (((Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m2 mT)) : ℕ) : ℝ) * ((2 ^ m1 * a1) * (2 ^ m1 * a1))
      + ((Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m1 mT)) : ℕ) : ℝ) * ((2 ^ m2 * a2) * (2 ^ m2 * a2))
      + ((Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m1 m2)) : ℕ) : ℝ) * ((2 ^ mT * t) * (2 ^ mT * t))) = _
  rw [cast_shl1, cast_shl1, cast_shl1, cast_shl1, cast_shl1]
  show (2 : ℝ) ^ (2 * (m1 + m2 + mT)) + 2 ^ (m1 + m2 + mT + 1) * _
    - (2 ^ (2 * (m2 + mT)) * _ + 2 ^ (2 * (m1 + mT)) * _ + 2 ^ (2 * (m1 + m2)) * _) = _
  ring

/-! ## The end points -/

theorem locPair_nonneg {P : Par} {cls ip iq m : ℕ} {c : PairConst} (hc : cond (Nat.beq cls 0) P.cA P.cB = c)
    {M N N' Rv : ℝ} {mP mQ : ℕ} (hpt : PairPt c mP mQ M N Rv) (hRv : 0 ≤ Rv)
    (hmaj : clsMaj (realOps W L y) P cls ip = 2 ^ m * M) (hmin : clsMin (realOps W L y) P cls iq = 2 ^ m * N')
    (hN : N' ^ 2 = N ^ 2) (hip : var (realOps W L y) ip = 2 ^ mP * (1 - M))
    (hiq : var (realOps W L y) iq ^ 2 = (2 ^ mQ * N) ^ 2) :
    ∀ g ∈ locPair (realOps W L y) P cls ip iq (2 ^ (2 * m) * Rv) m, 0 ≤ g := by
  intro g hg
  have hg' : g ∈ [2 ^ (2 * m) * Rv,
      ((Nat.mul c.etan (Nat.shiftLeft 1 (Nat.mul 2 m)) : ℕ) : ℝ) - (c.etad : ℝ) * (2 ^ (2 * m) * Rv),
      (c.aPn : ℝ) - (c.aPd : ℝ) * var (realOps W L y) ip,
      (c.aQ2n : ℝ) - (c.aQ2d : ℝ) * (var (realOps W L y) iq * var (realOps W L y) iq),
      (c.tn : ℝ) * (clsMaj (realOps W L y) P cls ip * clsMaj (realOps W L y) P cls ip)
        - (c.td : ℝ) * (clsMin (realOps W L y) P cls iq * clsMin (realOps W L y) P cls iq),
      ((Nat.mul c.g0 (Nat.shiftLeft 1 (Nat.mul 2 m)) : ℕ) : ℝ)
        - ((c.g1 : ℝ) * (2 ^ (2 * m) * Rv)
          + (c.g2 : ℝ) * (clsMin (realOps W L y) P cls iq * clsMin (realOps W L y) P cls iq))] := by
    rw [← hc]
    exact hg
  have h2 : (0 : ℝ) ≤ 2 ^ (2 * m) := by positivity
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
  rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact mul_nonneg h2 hRv
  · rw [cast_mul_shl]
    show (0 : ℝ) ≤ c.etan * 2 ^ (2 * m) - c.etad * (2 ^ (2 * m) * Rv)
    have e : (c.etan : ℝ) * 2 ^ (2 * m) - c.etad * (2 ^ (2 * m) * Rv) = 2 ^ (2 * m) * ((c.etan : ℝ) - c.etad * Rv) := by ring
    rw [e]
    exact mul_nonneg h2 (by linarith [hpt.eta])
  · rw [hip]
    linarith [hpt.major]
  · rw [← sq, hiq]
    linarith [hpt.minor]
  · rw [hmaj, hmin]
    have e : (c.tn : ℝ) * (2 ^ m * M * (2 ^ m * M)) - c.td * (2 ^ m * N' * (2 ^ m * N'))
        = (2 ^ m) ^ 2 * ((c.tn : ℝ) * M ^ 2 - c.td * N' ^ 2) := by ring
    rw [e, hN]
    exact mul_nonneg (by positivity) (by linarith [hpt.cone])
  · rw [cast_mul_shl, hmin]
    show (0 : ℝ) ≤ c.g0 * 2 ^ (2 * m) - (c.g1 * (2 ^ (2 * m) * Rv) + c.g2 * (2 ^ m * N' * (2 ^ m * N')))
    have e : (c.g0 : ℝ) * 2 ^ (2 * m) - (c.g1 * (2 ^ (2 * m) * Rv) + c.g2 * (2 ^ m * N' * (2 ^ m * N')))
        = 2 ^ (2 * m) * ((c.g0 : ℝ) - (c.g1 * Rv + c.g2 * N' ^ 2)) := by ring
    rw [e, hN]
    exact mul_nonneg h2 (by linarith [hpt.gs])

theorem locRing_nonneg {P : Par} {cls ip iq : ℕ} {Rv pu pv : ℝ} (hRv : 0 ≤ Rv)
    (hip : var (realOps W L y) ip ^ 2 = pu ^ 2) (hiq : var (realOps W L y) iq ^ 2 = pv ^ 2)
    (h1 : (P.eR2d : ℝ) * pu ^ 2 ≤ P.eR2n) (h2 : (P.eR2d : ℝ) * pv ^ 2 ≤ P.eR2n)
    (h3 : (P.Gd : ℝ) * (pu ^ 2 + pv ^ 2) ≤ P.Gn)
    (h4 : (nth P.lowN (cls - 2) : ℝ) ≤ nth P.lowD (cls - 2) * (pu ^ 2 + pv ^ 2)) :
    ∀ g ∈ locRing (realOps W L y) P cls ip iq Rv, 0 ≤ g := by
  intro g hg
  have hg' : g ∈ [Rv,
      (P.eR2n : ℝ) - (P.eR2d : ℝ) * (var (realOps W L y) ip * var (realOps W L y) ip),
      (P.eR2n : ℝ) - (P.eR2d : ℝ) * (var (realOps W L y) iq * var (realOps W L y) iq),
      (P.Gn : ℝ) - (P.Gd : ℝ) * (var (realOps W L y) ip * var (realOps W L y) ip
        + var (realOps W L y) iq * var (realOps W L y) iq),
      (nth P.lowD (Nat.sub cls 2) : ℝ) * (var (realOps W L y) ip * var (realOps W L y) ip
        + var (realOps W L y) iq * var (realOps W L y) iq) - (nth P.lowN (Nat.sub cls 2) : ℝ)] := hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
  rw [← sq, ← sq] at hg'
  rw [hip, hiq] at hg'
  rcases hg' with rfl | rfl | rfl | rfl | rfl
  · exact hRv
  · linarith
  · linarith
  · linarith
  · have : (nth P.lowN (cls - 2) : ℝ) ≤ nth P.lowD (cls - 2) * (pu ^ 2 + pv ^ 2) := h4
    show (0 : ℝ) ≤ (nth P.lowD (cls - 2) : ℝ) * (pu ^ 2 + pv ^ 2) - (nth P.lowN (cls - 2) : ℝ)
    linarith

/-- **An end point of the pair A**: the label `l < 2` at the variables `ip`, `iq`, with the sign `τ` of its
second class coordinate. -/
theorem endA {P : Par} {C : Conf} {l : ℕ} (hl : l < 2)
    (hpt : PairPt P.cA P.mAP P.mAQ (eps l * C.u l) (C.v l) (C.R l)) {ip iq : ℕ} {τ : ℝ} (hτ : τ ^ 2 = 1)
    (hip : var (realOps W L y) ip = cp P C l) (hiq : var (realOps W L y) iq = τ * cq P C l) (sg : ℕ) :
    clsU (realOps W L y) P 0 sg ip iq = 2 ^ clsM P 0 * ((sgA sg * eps l) * C.u l)
      ∧ clsV (realOps W L y) P 0 sg ip iq = 2 ^ clsM P 0 * (τ * C.v l)
      ∧ ∀ g ∈ locEnd (realOps W L y) P 0 ip iq (2 ^ (2 * clsM P 0) * C.R l) (clsM P 0), 0 ≤ g := by
  have hcp : cp P C l = 2 ^ P.mAP * (1 - eps l * C.u l) := by
    unfold cp
    rw [if_pos hl]
  have hcq : cq P C l = 2 ^ P.mAQ * C.v l := by
    unfold cq
    rw [if_pos hl]
  have hm : clsM P 0 = max P.mAP P.mAQ := maxN_eq _ _
  have h1 : P.mAP ≤ clsM P 0 := by
    rw [hm]
    exact le_max_left _ _
  have h2 : P.mAQ ≤ clsM P 0 := by
    rw [hm]
    exact le_max_right _ _
  have e1 : (2 : ℝ) ^ clsM P 0 = 2 ^ (Nat.sub (clsM P 0) P.mAP) * 2 ^ P.mAP := by
    rw [← pow_add]
    congr 1
    exact (Nat.sub_add_cancel h1).symm
  have e2 : (2 : ℝ) ^ clsM P 0 = 2 ^ (Nat.sub (clsM P 0) P.mAQ) * 2 ^ P.mAQ := by
    rw [← pow_add]
    congr 1
    exact (Nat.sub_add_cancel h2).symm
  have hmaj : clsMaj (realOps W L y) P 0 ip = 2 ^ clsM P 0 * (eps l * C.u l) := by
    show ((Nat.shiftLeft 1 (clsM P 0) : ℕ) : ℝ)
      - ((Nat.shiftLeft 1 (Nat.sub (clsM P 0) P.mAP) : ℕ) : ℝ) * var (realOps W L y) ip = _
    rw [cast_shl1, cast_shl1, hip, hcp, e1]
    ring
  have hmin : clsMin (realOps W L y) P 0 iq = 2 ^ clsM P 0 * (τ * C.v l) := by
    show ((Nat.shiftLeft 1 (Nat.sub (clsM P 0) P.mAQ) : ℕ) : ℝ) * var (realOps W L y) iq = _
    rw [cast_shl1, hiq, hcq, e2]
    ring
  refine ⟨?_, hmin, ?_⟩
  · show signed (realOps W L y) sg (clsMaj (realOps W L y) P 0 ip) = _
    rw [signed_real, hmaj]
    ring
  · show ∀ g ∈ locPair (realOps W L y) P 0 ip iq (2 ^ (2 * clsM P 0) * C.R l) (clsM P 0), 0 ≤ g
    refine locPair_nonneg (c := P.cA) rfl hpt (C.R_nonneg l) hmaj hmin ?_ (by rw [hip, hcp]) ?_
    · rw [mul_pow, hτ, one_mul]
    · rw [hiq, hcq, mul_pow, hτ, one_mul]

/-- **An end point of the pair B**: the label `2 ≤ l < 4`. -/
theorem endB {P : Par} {C : Conf} {l : ℕ} (hl2 : 2 ≤ l) (hl : l < 4)
    (hpt : PairPt P.cB P.mBP P.mBQ (eps l * C.v l) (C.u l) (C.R l)) {ip iq : ℕ} {τ : ℝ} (hτ : τ ^ 2 = 1)
    (hip : var (realOps W L y) ip = cp P C l) (hiq : var (realOps W L y) iq = τ * cq P C l) (sg : ℕ) :
    clsU (realOps W L y) P 1 sg ip iq = 2 ^ clsM P 1 * (τ * C.u l)
      ∧ clsV (realOps W L y) P 1 sg ip iq = 2 ^ clsM P 1 * ((sgA sg * eps l) * C.v l)
      ∧ ∀ g ∈ locEnd (realOps W L y) P 1 ip iq (2 ^ (2 * clsM P 1) * C.R l) (clsM P 1), 0 ≤ g := by
  have hcp : cp P C l = 2 ^ P.mBP * (1 - eps l * C.v l) := by
    unfold cp
    rw [if_neg (by omega), if_pos hl]
  have hcq : cq P C l = 2 ^ P.mBQ * C.u l := by
    unfold cq
    rw [if_neg (by omega), if_pos hl]
  have hm : clsM P 1 = max P.mBP P.mBQ := maxN_eq _ _
  have h1 : P.mBP ≤ clsM P 1 := by
    rw [hm]
    exact le_max_left _ _
  have h2 : P.mBQ ≤ clsM P 1 := by
    rw [hm]
    exact le_max_right _ _
  have e1 : (2 : ℝ) ^ clsM P 1 = 2 ^ (Nat.sub (clsM P 1) P.mBP) * 2 ^ P.mBP := by
    rw [← pow_add]
    congr 1
    exact (Nat.sub_add_cancel h1).symm
  have e2 : (2 : ℝ) ^ clsM P 1 = 2 ^ (Nat.sub (clsM P 1) P.mBQ) * 2 ^ P.mBQ := by
    rw [← pow_add]
    congr 1
    exact (Nat.sub_add_cancel h2).symm
  have hmaj : clsMaj (realOps W L y) P 1 ip = 2 ^ clsM P 1 * (eps l * C.v l) := by
    show ((Nat.shiftLeft 1 (clsM P 1) : ℕ) : ℝ)
      - ((Nat.shiftLeft 1 (Nat.sub (clsM P 1) P.mBP) : ℕ) : ℝ) * var (realOps W L y) ip = _
    rw [cast_shl1, cast_shl1, hip, hcp, e1]
    ring
  have hmin : clsMin (realOps W L y) P 1 iq = 2 ^ clsM P 1 * (τ * C.u l) := by
    show ((Nat.shiftLeft 1 (Nat.sub (clsM P 1) P.mBQ) : ℕ) : ℝ) * var (realOps W L y) iq = _
    rw [cast_shl1, hiq, hcq, e2]
    ring
  refine ⟨hmin, ?_, ?_⟩
  · show signed (realOps W L y) sg (clsMaj (realOps W L y) P 1 ip) = _
    rw [signed_real, hmaj]
    ring
  · show ∀ g ∈ locPair (realOps W L y) P 1 ip iq (2 ^ (2 * clsM P 1) * C.R l) (clsM P 1), 0 ≤ g
    refine locPair_nonneg (c := P.cB) rfl hpt (C.R_nonneg l) hmaj hmin ?_ (by rw [hip, hcp]) ?_
    · rw [mul_pow, hτ, one_mul]
    · rw [hiq, hcq, mul_pow, hτ, one_mul]

/-- **A ring end point**: the label `4 ≤ l` of the class `cls ≥ 2`, with the signs `τp`, `τq` of its class
coordinates. -/
theorem endR {P : Par} {C : Conf} {l cls : ℕ} (hl : 4 ≤ l) (hcls : 2 ≤ cls)
    (h1 : (P.eR2d : ℝ) * C.u l ^ 2 ≤ P.eR2n) (h2 : (P.eR2d : ℝ) * C.v l ^ 2 ≤ P.eR2n)
    (h3 : (P.Gd : ℝ) * (C.u l ^ 2 + C.v l ^ 2) ≤ P.Gn)
    (h4 : (nth P.lowN (cls - 2) : ℝ) ≤ nth P.lowD (cls - 2) * (C.u l ^ 2 + C.v l ^ 2))
    {ip iq : ℕ} {τp τq : ℝ} (hτp : τp ^ 2 = 1) (hτq : τq ^ 2 = 1)
    (hip : var (realOps W L y) ip = τp * cp P C l) (hiq : var (realOps W L y) iq = τq * cq P C l) (sg : ℕ) :
    clsU (realOps W L y) P cls sg ip iq = 2 ^ clsM P cls * (τp * C.u l)
      ∧ clsV (realOps W L y) P cls sg ip iq = 2 ^ clsM P cls * (τq * C.v l)
      ∧ ∀ g ∈ locEnd (realOps W L y) P cls ip iq (2 ^ (2 * clsM P cls) * C.R l) (clsM P cls), 0 ≤ g := by
  have hcp : cp P C l = C.u l := by
    unfold cp
    rw [if_neg (by omega), if_neg (by omega)]
  have hcq : cq P C l = C.v l := by
    unfold cq
    rw [if_neg (by omega), if_neg (by omega)]
  have b0 : Nat.beq cls 0 = false := beq_false_of_ne (by omega)
  have b1 : Nat.beq cls 1 = false := beq_false_of_ne (by omega)
  have hm : clsM P cls = 0 := by
    unfold clsM
    rw [b0, b1]
    rfl
  have hb : Nat.blt cls 2 = false := by
    cases hbb : Nat.blt cls 2
    · rfl
    · exact absurd (lt_of_blt hbb) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · unfold clsU
    rw [b0, b1, hm]
    show var (realOps W L y) ip = _
    rw [hip, hcp]
    ring
  · unfold clsV
    rw [b0, b1, hm]
    show var (realOps W L y) iq = _
    rw [hiq, hcq]
    ring
  · unfold locEnd
    rw [hb]
    show ∀ g ∈ locRing (realOps W L y) P cls ip iq (2 ^ (2 * clsM P cls) * C.R l), 0 ≤ g
    refine locRing_nonneg (pu := C.u l) (pv := C.v l) (mul_nonneg (by positivity) (C.R_nonneg l)) ?_ ?_ h1 h2 h3 h4
    · rw [hip, hcp, mul_pow, hτp, one_mul]
    · rw [hiq, hcq, mul_pow, hτq, one_mul]

/-! ## The facts of a pair -/

/-- **The facts of a pair** `i < j` of labels with the record type `h`, at the data `y` of the pair: `σu`, `σv`
are the common signs of the coordinates of the two end points, and `(m0, m1)` is the point of the minorant. -/
structure RecFacts (P : Par) (heads : List RecH) (C : Conf) (i j : ℕ) (h : RecH) (y : Fin 5 → ℝ) (σu σv m0 m1 : ℝ) :
    Prop where
  cube : ∀ k, |y k| ≤ 1
  su : σu ^ 2 = 1
  sv : σv ^ 2 = 1
  unit_i : C.u i ^ 2 + C.v i ^ 2 + C.ξ i ^ 2 + C.η i ^ 2 = 1
  unit_j : C.u j ^ 2 + C.v j ^ 2 + C.ξ j ^ 2 + C.η j ^ 2 = 1
  U1 : ∀ (W : ℕ) (L : Lay), clsU (realOps W L y) P h.c1 h.s1 0 1 = 2 ^ clsM P h.c1 * (σu * C.u i)
  V1 : ∀ (W : ℕ) (L : Lay), clsV (realOps W L y) P h.c1 h.s1 0 1 = 2 ^ clsM P h.c1 * (σv * C.v i)
  U2 : ∀ (W : ℕ) (L : Lay), clsU (realOps W L y) P h.c2 h.s2 (i2p h) (i2q h) = 2 ^ clsM P h.c2 * (σu * C.u j)
  V2 : ∀ (W : ℕ) (L : Lay), clsV (realOps W L y) P h.c2 h.s2 (i2p h) (i2q h) = 2 ^ clsM P h.c2 * (σv * C.v j)
  T : ∀ (W : ℕ) (L : Lay), recT (realOps W L y) P h (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
    (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j)) = 2 ^ recMT P h * C.t i j
  loc1 : ∀ (W : ℕ) (L : Lay), ∀ g ∈ locEnd (realOps W L y) P h.c1 0 1 (2 ^ (2 * clsM P h.c1) * C.R i) (clsM P h.c1), 0 ≤ g
  loc2 : ∀ (W : ℕ) (L : Lay),
    ∀ g ∈ locEnd (realOps W L y) P h.c2 (i2p h) (i2q h) (2 ^ (2 * clsM P h.c2) * C.R j) (clsM P h.c2), 0 ≤ g
  locS : (Nat.ble 2 h.kind && Nat.ble h.kind 4) = true → (h.aS2d : ℝ) * y 4 ^ 2 ≤ h.aS2n
  locD : Nat.beq h.kind 1 = true → clsM P h.c2 = clsM P h.c1 ∧ C.R j = C.R i
    ∧ (P.dird : ℝ) * (σu * C.u i - σu * C.u j) ^ 2 ≤ P.dirn * (σv * C.v i - σv * C.v j) ^ 2
  hm0 : ∀ (W : ℕ) (L : Lay), Nat.beq h.hform 0 = true →
    recHm (realOps W L y) P h (2 ^ recMT P h * C.t i j) (recMT P h) = poly2 P.wP h.hex h.hp h.hn m0 m1
  hm1 : ∀ (W : ℕ) (L : Lay), Nat.beq h.hform 0 = false →
    2 ^ (h.hm + recMT P h) * recHm (realOps W L y) P h (2 ^ recMT P h * C.t i j) (recMT P h)
      = 2 ^ ((h.hm + recMT P h) * len h.hex) * poly2 P.wP h.hex h.hp h.hn m0 m1
  inner : ∀ (W : ℕ) (L : Lay), ∀ blks ∈ P.kblocks,
    innerK (realOps W L y) h.c1 h.s1 0 1 h.c2 h.s2 (i2p h) (i2q h) blks 0 = Kb P C i j blks
  pi1 : ∀ (W : ℕ) (L : Lay), dotS (realOps W L y) P.wP 0 0 0 1 h.p1ex h.p1p h.p1n = piN P heads C i j
  pi2 : ∀ (W : ℕ) (L : Lay), dotS (realOps W L y) P.wP 0 0 (i2p h) (i2q h) h.p2ex h.p2p h.p2n = piN P heads C j i
  mcube : |m0| ≤ 1 ∧ |m1| ≤ 1
  mT : ∀ (W : ℕ) (L : Lay), minoT (realOps W L ![m0, m1, 0, 0, 0]) h = 2 ^ minoMM h * C.t i j
  mlocs : ∀ (W : ℕ) (L : Lay),
    ∀ g ∈ minoLocs (realOps W L ![m0, m1, 0, 0, 0]) P h (2 ^ minoMM h * C.t i j) (minoMM h), 0 ≤ g
  mcodes : ∀ c ∈ h.hex, c < 256
  ivlo : (h.lop : ℝ) - h.lon ≤ h.lod * C.t i j
  ivhi : (h.hid : ℝ) * C.t i j ≤ (h.hip : ℝ) - h.hin
  hi1 : h.hip < h.hid + h.hin
  hid1 : 1 ≤ h.hid

section

variable {P : Par} {heads : List RecH} {C : Conf} {i j : ℕ} {h : RecH} {y : Fin 5 → ℝ} {σu σv m0 m1 : ℝ}

theorem recVal_eq {α : Type} (o : Ops α) (P : Par) (h : RecH) (x : RecX) :
    recVal o P h x = recValK o P h x (i2p h) (i2q h) (clsM P h.c1) (clsM P h.c2) (recMT P h)
      (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1) (clsU o P h.c2 h.s2 (i2p h) (i2q h))
      (clsV o P h.c2 h.s2 (i2p h) (i2q h))
      (recT o P h (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1) (clsU o P h.c2 h.s2 (i2p h) (i2q h))
        (clsV o P h.c2 h.s2 (i2p h) (i2q h)))
      (clsR o (clsM P h.c1) (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1))
      (clsR o (clsM P h.c2) (clsU o P h.c2 h.s2 (i2p h) (i2q h)) (clsV o P h.c2 h.s2 (i2p h) (i2q h))) := rfl

theorem recValK_eq {α : Type} (o : Ops α) (P : Par) (h : RecH) (x : RecX) (i2p i2q m1 m2 mT : ℕ)
    (U1 V1 U2 V2 T R1 R2 : α) :
    recValK o P h x i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
      = o.sub (recLhs o P h x i2p i2q mT T (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2))
        (cond (Nat.beq h.kind 1)
          (o.add (sosGo o x.ws (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
              (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)) (o.nat 0))
            (o.smul (Nat.shiftLeft 1 x.aL) (o.mul (o.sub R2 R1) (dot5 o P.wP x.lex x.lp x.ln))))
          (sosGo o x.ws (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
            (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)) (o.nat 0))) := rfl

theorem recLhs_real (P : Par) (h : RecH) (x : RecX) (i2p i2q mT : ℕ) (T H Wt : ℝ) :
    recLhs (realOps W L y) P h x i2p i2q mT T H Wt
      = 2 ^ x.aH * recHm (realOps W L y) P h T mT + h.cn * 2 ^ x.aC
        - (h.cp * 2 ^ x.aC
          + kernGo (realOps W L y) h.c1 h.s1 0 1 h.c2 h.s2 i2p i2q P.kblocks
              (qList (realOps W L y) H Wt mT (lenB P.kblocks)) x.aK 0
          + 2 ^ x.aP * (dotS (realOps W L y) P.wP 0 0 0 1 h.p1ex h.p1p h.p1n
              + dotS (realOps W L y) P.wP 0 0 i2p i2q h.p2ex h.p2p h.p2n)) := by
  show ((Nat.shiftLeft 1 x.aH : ℕ) : ℝ) * recHm (realOps W L y) P h T mT + ((Nat.shiftLeft h.cn x.aC : ℕ) : ℝ)
    - (((Nat.shiftLeft h.cp x.aC : ℕ) : ℝ)
      + kernGo (realOps W L y) h.c1 h.s1 0 1 h.c2 h.s2 i2p i2q P.kblocks
          (qList (realOps W L y) H Wt mT (lenB P.kblocks)) x.aK ((0 : ℕ) : ℝ)
      + ((Nat.shiftLeft 1 x.aP : ℕ) : ℝ) * (dotS (realOps W L y) P.wP 0 0 0 1 h.p1ex h.p1p h.p1n
          + dotS (realOps W L y) P.wP 0 0 i2p i2q h.p2ex h.p2p h.p2n)) = _
  rw [cast_shl1, cast_shl1, cast_shl, cast_shl, Nat.cast_zero]

/-- The weights of the record are nonnegative at the data of the pair. -/
theorem recLocs_nonneg (F : RecFacts P heads C i j h y σu σv m0 m1) (W : ℕ) (L : Lay) :
    ∀ g ∈ recLocs (realOps W L y) P h (i2p h) (i2q h) (clsM P h.c1) (clsM P h.c2) (recMT P h)
        (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
        (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j))
        (2 ^ recMT P h * C.t i j) (2 ^ (2 * clsM P h.c1) * C.R i) (2 ^ (2 * clsM P h.c2) * C.R j)
        (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
        ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j)), 0 ≤ g := by
  intro g hg
  have hg' : g ∈ ((1 : ℕ) : ℝ) :: (locEnd (realOps W L y) P h.c1 0 1 (2 ^ (2 * clsM P h.c1) * C.R i) (clsM P h.c1)
      ++ (cond (Nat.beq h.kind 0) []
          (locEnd (realOps W L y) P h.c2 (i2p h) (i2q h) (2 ^ (2 * clsM P h.c2) * C.R j) (clsM P h.c2))
        ++ (locT (realOps W L y) h (2 ^ recMT P h * C.t i j) (recMT P h)
          :: (cond (Nat.ble 2 h.kind && Nat.ble h.kind 4)
              [(h.aS2n : ℝ) - (h.aS2d : ℝ) * (var (realOps W L y) 4 * var (realOps W L y) 4)] []
            ++ (locG3 (realOps W L y) (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c2 * (σu * C.u j))
                (2 ^ recMT P h * C.t i j) (clsM P h.c1) (clsM P h.c2) (recMT P h)
              :: locG3 (realOps W L y) (2 ^ clsM P h.c1 * (σv * C.v i)) (2 ^ clsM P h.c2 * (σv * C.v j))
                (2 ^ recMT P h * C.t i j) (clsM P h.c1) (clsM P h.c2) (recMT P h)
              :: (cond (Nat.ble 2 h.kind)
                  [((Nat.shiftLeft 1 (Nat.mul 2 (recMT P h)) : ℕ) : ℝ)
                      * ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
                    - (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
                      * (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)] []
                ++ cond (Nat.beq h.kind 1)
                  [(P.dirn : ℝ) * ((2 ^ clsM P h.c1 * (σv * C.v i) - 2 ^ clsM P h.c2 * (σv * C.v j))
                        * (2 ^ clsM P h.c1 * (σv * C.v i) - 2 ^ clsM P h.c2 * (σv * C.v j)))
                    - (P.dird : ℝ) * ((2 ^ clsM P h.c1 * (σu * C.u i) - 2 ^ clsM P h.c2 * (σu * C.u j))
                        * (2 ^ clsM P h.c1 * (σu * C.u i) - 2 ^ clsM P h.c2 * (σu * C.u j)))] [])))))) := hg
  simp only [List.mem_cons, List.mem_append] at hg'
  rcases hg' with rfl | hg' | hg' | rfl | hg' | rfl | rfl | hg' | hg'
  · simp
  · exact F.loc1 W L g hg'
  · rcases mem_cond hg' with ⟨_, hm⟩ | ⟨_, hm⟩
    · exact absurd hm List.not_mem_nil
    · exact F.loc2 W L g hm
  · exact locT_nonneg h (recMT P h) F.ivlo F.ivhi
  · rcases mem_cond hg' with ⟨hb, hm⟩ | ⟨_, hm⟩
    · rw [List.mem_singleton] at hm
      subst hm
      rw [var4, ← sq]
      linarith [F.locS hb]
    · exact absurd hm List.not_mem_nil
  · rw [locG3_real]
    refine mul_nonneg (by positivity) ?_
    have e : 1 + 2 * (σu * C.u i) * (σu * C.u j) * C.t i j - (σu * C.u i) ^ 2 - (σu * C.u j) ^ 2 - C.t i j ^ 2
        = 1 + 2 * C.u i * C.u j * C.t i j - C.u i ^ 2 - C.u j ^ 2 - C.t i j ^ 2 := by
      linear_combination (2 * C.u i * C.u j * C.t i j - C.u i ^ 2 - C.u j ^ 2) * F.su
    rw [e]
    exact gram_nonneg F.unit_i F.unit_j rfl
  · rw [locG3_real]
    refine mul_nonneg (by positivity) ?_
    have e : 1 + 2 * (σv * C.v i) * (σv * C.v j) * C.t i j - (σv * C.v i) ^ 2 - (σv * C.v j) ^ 2 - C.t i j ^ 2
        = 1 + 2 * C.v i * C.v j * C.t i j - C.v i ^ 2 - C.v j ^ 2 - C.t i j ^ 2 := by
      linear_combination (2 * C.v i * C.v j * C.t i j - C.v i ^ 2 - C.v j ^ 2) * F.sv
    rw [e]
    refine gram_nonneg (u := C.v i) (v := C.u i) (ξ := C.ξ i) (η := C.η i) (u' := C.v j) (v' := C.u j) (ξ' := C.ξ j)
      (η' := C.η j) (by linarith [F.unit_i]) (by linarith [F.unit_j]) ?_
    unfold Conf.t
    ring
  · rcases mem_cond hg' with ⟨_, hm⟩ | ⟨_, hm⟩
    · rw [List.mem_singleton] at hm
      subst hm
      rw [cast_shl1]
      show (0 : ℝ) ≤ 2 ^ (2 * recMT P h) * ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
        - (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
          * (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
      have e : (2 : ℝ) ^ (2 * recMT P h) * ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
          - (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
            * (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
          = (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2)) ^ 2 * (C.R i * C.R j - C.Hh i j ^ 2) := by ring
      rw [e]
      exact mul_nonneg (by positivity) (gram2_nonneg C i j)
    · exact absurd hm List.not_mem_nil
  · rcases mem_cond hg' with ⟨hb, hm⟩ | ⟨_, hm⟩
    · rw [List.mem_singleton] at hm
      subst hm
      obtain ⟨hmm, _, hd⟩ := F.locD hb
      rw [hmm]
      have e : (P.dirn : ℝ) * ((2 ^ clsM P h.c1 * (σv * C.v i) - 2 ^ clsM P h.c1 * (σv * C.v j))
            * (2 ^ clsM P h.c1 * (σv * C.v i) - 2 ^ clsM P h.c1 * (σv * C.v j)))
          - (P.dird : ℝ) * ((2 ^ clsM P h.c1 * (σu * C.u i) - 2 ^ clsM P h.c1 * (σu * C.u j))
            * (2 ^ clsM P h.c1 * (σu * C.u i) - 2 ^ clsM P h.c1 * (σu * C.u j)))
          = (2 ^ clsM P h.c1) ^ 2 * ((P.dirn : ℝ) * (σv * C.v i - σv * C.v j) ^ 2
            - (P.dird : ℝ) * (σu * C.u i - σu * C.u j) ^ 2) := by ring
      rw [e]
      exact mul_nonneg (by positivity) (by linarith)
    · exact absurd hm List.not_mem_nil

/-- The scales of a record identity. -/
theorem scales_of {x : RecX} (hsc : recScalesOk P h x = true) {r pv : ℝ} (h0 : Nat.beq h.hform 0 = true → r = pv)
    (h1 : Nat.beq h.hform 0 = false →
      2 ^ (h.hm + recMT P h) * r = 2 ^ ((h.hm + recMT P h) * len h.hex) * pv) :
    2 ^ x.aH * r = 2 ^ x.E * (pv / 2 ^ P.sP) ∧ x.aC + P.sP = x.E ∧ x.aP + P.sP = x.E
      ∧ kScalesGo h.c1 h.c2 (Nat.add (Nat.add (recMT P h) (clsM P h.c1)) (clsM P h.c2)) (Nat.succ x.E) P.kblocks
          x.aK P.sK 0 = true := by
  have hsc' : (Nat.beq (Nat.add x.aC P.sP) x.E && Nat.beq (Nat.add x.aP P.sP) x.E
      && cond (Nat.beq h.hform 0) (Nat.beq (Nat.add x.aH P.sP) x.E)
          (Nat.ble 1 (len h.hex)
            && Nat.beq (Nat.add (Nat.add x.aH P.sP) (Nat.mul (Nat.add h.hm (recMT P h)) (Nat.pred (len h.hex)))) x.E)
      && kScalesGo h.c1 h.c2 (Nat.add (Nat.add (recMT P h) (clsM P h.c1)) (clsM P h.c2)) (Nat.succ x.E) P.kblocks
          x.aK P.sK 0) = true := hsc
  simp only [Bool.and_eq_true] at hsc'
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := hsc'
  have ha : x.aC + P.sP = x.E := Nat.eq_of_beq_eq_true a
  have hb : x.aP + P.sP = x.E := Nat.eq_of_beq_eq_true b
  refine ⟨?_, ha, hb, d⟩
  have hS : (2 : ℝ) ^ P.sP ≠ 0 := by positivity
  cases hf : Nat.beq h.hform 0
  · rw [hf] at c
    have c' : (Nat.ble 1 (len h.hex)
        && Nat.beq (Nat.add (Nat.add x.aH P.sP) (Nat.mul (Nat.add h.hm (recMT P h)) (Nat.pred (len h.hex)))) x.E)
        = true := c
    rw [Bool.and_eq_true] at c'
    obtain ⟨n, hn⟩ : ∃ n, len h.hex = n + 1 := ⟨len h.hex - 1, by
      have := Nat.le_of_ble_eq_true c'.1
      omega⟩
    have hE : x.aH + P.sP + (h.hm + recMT P h) * n = x.E := by
      have := Nat.eq_of_beq_eq_true c'.2
      rw [hn] at this
      exact this
    have h1' := h1 hf
    rw [hn] at h1'
    have hr : r = 2 ^ ((h.hm + recMT P h) * n) * pv := by
      have h2 : (2 : ℝ) ^ (h.hm + recMT P h) ≠ 0 := by positivity
      apply mul_left_cancel₀ h2
      rw [h1']
      ring
    rw [hr, ← hE, pow_add, pow_add, mul_div_assoc', eq_div_iff hS]
    ring
  · rw [hf] at c
    have hE : x.aH + P.sP = x.E := Nat.eq_of_beq_eq_true c
    rw [h0 hf, ← hE, pow_add, mul_div_assoc', eq_div_iff hS]
    ring

/-- **The record of a pair.** -/
theorem rec_part (F : RecFacts P heads C i j h y σu σv m0 m1) {x : RecX} (hL : LayoutInj x.L)
    (hx : recordOk P h x = true) :
    ((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
        - x.rho / 2 ^ x.E
      ≤ poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP := by
  have hrec := recordOk_sound hL hx F.cube
  obtain ⟨hpv, haC, haP, hks⟩ := scales_of (recordOk_scales hx) (F.hm0 x.W x.L) (F.hm1 x.W x.L)
  have hR1 : clsR (realOps x.W x.L y) (clsM P h.c1) (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
      = 2 ^ (2 * clsM P h.c1) * C.R i := clsR_real _ F.su F.sv F.unit_i
  have hR2 : clsR (realOps x.W x.L y) (clsM P h.c2) (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j))
      = 2 ^ (2 * clsM P h.c2) * C.R j := clsR_real _ F.su F.sv F.unit_j
  have hH : recHv (realOps x.W x.L y) (clsM P h.c1) (clsM P h.c2) (recMT P h)
      (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
      (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j)) (2 ^ recMT P h * C.t i j)
      = 2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j := recHv_real _ _ _ F.su F.sv (t_eq C i j)
  rw [recVal_eq, F.U1, F.V1, F.U2, F.V2, F.T, hR1, hR2, recValK_eq, hH] at hrec
  have hS := sosGo_nonneg (W := x.W) (L := x.L) (y := y) x.ws _ ((0 : ℕ) : ℝ) (recLocs_nonneg F x.W x.L)
    (Nat.cast_nonneg 0)
  -- the term of the ideal vanishes
  have hval : |recLhs (realOps x.W x.L y) P h x (i2p h) (i2q h) (recMT P h) (2 ^ recMT P h * C.t i j)
        (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
        ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
      - sosGo (realOps x.W x.L y) x.ws (recLocs (realOps x.W x.L y) P h (i2p h) (i2q h) (clsM P h.c1) (clsM P h.c2)
          (recMT P h) (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
          (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j))
          (2 ^ recMT P h * C.t i j) (2 ^ (2 * clsM P h.c1) * C.R i) (2 ^ (2 * clsM P h.c2) * C.R j)
          (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
          ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))) ((0 : ℕ) : ℝ)| ≤ (x.rho : ℝ) := by
    cases hk : Nat.beq h.kind 1
    · rw [hk] at hrec
      exact hrec
    · rw [hk] at hrec
      obtain ⟨hmm, hRR, _⟩ := F.locD hk
      have hz : (realOps x.W x.L y).smul (Nat.shiftLeft 1 x.aL)
          ((realOps x.W x.L y).mul ((realOps x.W x.L y).sub (2 ^ (2 * clsM P h.c2) * C.R j) (2 ^ (2 * clsM P h.c1) * C.R i))
            (dot5 (realOps x.W x.L y) P.wP x.lex x.lp x.ln)) = 0 := by
        show ((Nat.shiftLeft 1 x.aL : ℕ) : ℝ) * ((2 ^ (2 * clsM P h.c2) * C.R j - 2 ^ (2 * clsM P h.c1) * C.R i)
          * dot5 (realOps x.W x.L y) P.wP x.lex x.lp x.ln) = 0
        rw [hmm, hRR]
        ring
      have hrec' : |(realOps x.W x.L y).sub _ ((realOps x.W x.L y).add _ _)| ≤ (x.rho : ℝ) := hrec
      rw [hz] at hrec'
      have e : ∀ a b : ℝ, (realOps x.W x.L y).sub a ((realOps x.W x.L y).add b 0) = a - b := fun a b => by
        show a - (b + 0) = a - b
        ring
      rw [e] at hrec'
      exact hrec'
  have hlow := (abs_le.1 hval).1
  rw [recLhs_real, hpv, F.pi1, F.pi2] at hlow
  have hk : kernGo (realOps x.W x.L y) h.c1 h.s1 0 1 h.c2 h.s2 (i2p h) (i2q h) P.kblocks
      (qList (realOps x.W x.L y) (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
        ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j)) (recMT P h) (lenB P.kblocks)) x.aK 0
      = 2 ^ (x.E + 1) * Kl P C i j := by
    have hW : (2 : ℝ) ^ (2 * recMT P h) * ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
        = 2 ^ (2 * (recMT P h + clsM P h.c1 + clsM P h.c2)) * (C.R i * C.R j) := by ring
    have key := kernGo_real (W := x.W) (L := x.L) (y := y) (c1 := h.c1) (s1 := h.s1) (i1p := 0) (i1q := 1) (c2 := h.c2)
      (s2 := h.s2) (i2p := i2p h) (i2q := i2q h) (E1 := Nat.succ x.E)
      (H := 2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j) (Hx := C.Hh i j) (ρ := C.R i * C.R j)
      (eH := recMT P h + clsM P h.c1 + clsM P h.c2) rfl hW P.kblocks x.aK P.sK 0
      ((0 : ℕ) : ℝ) ((1 : ℕ) : ℝ) 0 hks (by simp [Qr]) (fun k' hk' => absurd hk' (by omega))
    have key' : kernGo (realOps x.W x.L y) h.c1 h.s1 0 1 h.c2 h.s2 (i2p h) (i2q h) P.kblocks
        (qList (realOps x.W x.L y) (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
          ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j)) (recMT P h) (lenB P.kblocks)) x.aK 0
        = 0 + 2 ^ Nat.succ x.E * kernR (fun blks => innerK (realOps x.W x.L y) h.c1 h.s1 0 1 h.c2 h.s2 (i2p h) (i2q h) blks 0)
          (Qr (C.R i * C.R j) (C.Hh i j)) P.kblocks P.sK 0 := key
    rw [key', zero_add, kernR_congr (fun _ => rfl) P.kblocks (F.inner x.W x.L) P.sK 0]
    rfl
  rw [hk] at hlow
  -- the arithmetic of the scales
  have hE : (2 : ℝ) ^ x.E = 2 ^ x.aC * 2 ^ P.sP := by rw [← haC, pow_add]
  have hPC : x.aP = x.aC := by omega
  rw [hPC, pow_succ, hE] at hlow
  have hA : (0 : ℝ) < 2 ^ x.aC := by positivity
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  rw [hE]
  have key : (((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
      - x.rho / (2 ^ x.aC * 2 ^ P.sP) - poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP) * (2 ^ x.aC * 2 ^ P.sP)
      = ((h.cp : ℝ) - h.cn) * 2 ^ x.aC + 2 * Kl P C i j * (2 ^ x.aC * 2 ^ P.sP)
        + (piN P heads C i j + piN P heads C j i) * 2 ^ x.aC - x.rho
        - poly2 P.wP h.hex h.hp h.hn m0 m1 * 2 ^ x.aC := by
    field_simp
  have hle : (((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
      - x.rho / (2 ^ x.aC * 2 ^ P.sP) - poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP) * (2 ^ x.aC * 2 ^ P.sP) ≤ 0 := by
    rw [key]
    have e : (2 : ℝ) ^ x.aC * 2 ^ P.sP * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)
        = poly2 P.wP h.hex h.hp h.hn m0 m1 * 2 ^ x.aC := by
      field_simp
    rw [e] at hlow
    linarith
  have hpos : (0 : ℝ) < 2 ^ x.aC * 2 ^ P.sP := mul_pos hA hSP
  by_contra hc
  rw [not_le] at hc
  have := mul_pos (sub_pos.2 hc) hpos
  linarith

/-- **The minorant of a pair.** -/
theorem mino_part (F : RecFacts P heads C i j h y σu σv m0 m1) {mx : MinoX} (hLm : LayoutInj mx.L)
    (hmx : minoOk P h mx = true) :
    poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP
        - (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip))
      ≤ 1 / (2 - 2 * C.t i j) := by
  have hcube : ∀ k, |(![m0, m1, 0, 0, 0] : Fin 5 → ℝ) k| ≤ 1 := by
    intro k
    fin_cases k
    · exact F.mcube.1
    · exact F.mcube.2
    · simp
    · simp
    · simp
  have hmin := minoOk_sound hLm hmx hcube
  have hmx' : (Nat.beq (Nat.add (Nat.add mx.aH (minoMM h)) P.sP) (Nat.succ mx.E)
      && runOk mx.L mx.W mx.wr mx.rho mx.ws (minoVal (pairOps mx.W mx.L) P h mx) (minoVal (absOps mx.L) P h mx)
        (minoVal degOps P h mx) (minoVal (pdegOps mx.L.pm) P h mx) (minoVal (posOps mx.L) P h mx)
        (minoVal (clsOps mx.L.pv) P h mx)) = true := hmx
  rw [Bool.and_eq_true] at hmx'
  have hsc : mx.aH + minoMM h + P.sP = mx.E + 1 := Nat.eq_of_beq_eq_true hmx'.1
  have hd : dotS (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P.wP 0 0 0 1 h.hex h.hp h.hn
      = poly2 P.wP h.hex h.hp h.hn m0 m1 :=
    dotS_real0 (at01 ![m0, m1, 0, 0, 0]) P.wP h.hex F.mcodes h.hp h.hn
  have hS := sosGo_nonneg (W := mx.W) (L := mx.L) (y := ![m0, m1, 0, 0, 0]) mx.ws _ 0 (F.mlocs mx.W mx.L) le_rfl
  have hv : minoVal (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h mx
      = 2 ^ mx.E - 2 ^ mx.aH * ((2 ^ minoMM h - 2 ^ minoMM h * C.t i j) * poly2 P.wP h.hex h.hp h.hn m0 m1)
        - sosGo (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) mx.ws
          (minoLocs (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h (2 ^ minoMM h * C.t i j) (minoMM h)) 0 := by
    show ((Nat.shiftLeft 1 mx.E : ℕ) : ℝ)
      - ((Nat.shiftLeft 1 mx.aH : ℕ) : ℝ) * ((((Nat.shiftLeft 1 (minoMM h) : ℕ) : ℝ)
          - minoT (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) h)
        * dotS (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P.wP 0 0 0 1 h.hex h.hp h.hn)
      - sosGo (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) mx.ws
          (minoLocs (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h (minoT (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) h) (minoMM h))
          ((0 : ℕ) : ℝ) = _
    rw [F.mT mx.W mx.L, hd, cast_shl1, cast_shl1, cast_shl1, Nat.cast_zero]
  rw [hv] at hmin
  have hlow := (abs_le.1 hmin).1
  -- arithmetic
  have hE1 : (2 : ℝ) ^ mx.aH * 2 ^ minoMM h * 2 ^ P.sP = 2 * 2 ^ mx.E := by
    rw [← pow_add, ← pow_add, hsc, pow_succ]
    ring
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  have hEp : (0 : ℝ) < 2 ^ mx.E := by positivity
  have hρ : (0 : ℝ) ≤ mx.rho := Nat.cast_nonneg _
  have hidp : (1 : ℝ) ≤ h.hid := by exact_mod_cast F.hid1
  have hgp : (0 : ℝ) < (h.hid : ℝ) + h.hin - h.hip := by
    have : (h.hip : ℝ) < (h.hid : ℝ) + h.hin := by exact_mod_cast F.hi1
    linarith
  have hd0 : (0 : ℝ) < 1 - C.t i j := by
    have := F.ivhi
    nlinarith
  have hgd : (h.hid : ℝ) + h.hin - h.hip ≤ h.hid * (1 - C.t i j) := by
    have := F.ivhi
    linarith
  -- with `q = pv / 2 ^ sP`: `-rho ≤ 2 ^ E * (1 - 2 * (1 - t) * q)`
  have hq : -(mx.rho : ℝ) ≤ 2 ^ mx.E * (1 - 2 * (1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
    have e : (2 : ℝ) ^ mx.aH * ((2 ^ minoMM h - 2 ^ minoMM h * C.t i j) * poly2 P.wP h.hex h.hp h.hn m0 m1)
        = (2 ^ mx.aH * 2 ^ minoMM h * 2 ^ P.sP) * ((1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
      field_simp
    rw [e, hE1] at hlow
    linarith
  have h1 : poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP ≤ (2 ^ mx.E + mx.rho) / (2 * (1 - C.t i j) * 2 ^ mx.E) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2 : ((2 : ℝ) ^ mx.E + mx.rho) / (2 * (1 - C.t i j) * 2 ^ mx.E)
      = 1 / (2 - 2 * C.t i j) + mx.rho / (2 ^ (mx.E + 1) * (1 - C.t i j)) := by
    have hne : (2 : ℝ) - 2 * C.t i j ≠ 0 := by linarith
    have hne' : (1 : ℝ) - C.t i j ≠ 0 := by linarith
    rw [pow_succ]
    field_simp
  have h3 : (mx.rho : ℝ) / (2 ^ (mx.E + 1) * (1 - C.t i j))
      ≤ (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hgd (mul_nonneg hρ (by positivity : (0 : ℝ) ≤ 2 ^ (mx.E + 1)))
    linarith
  linarith

/-- **The inequality of a pair**: the energy of the pair is at least the constant of its record type, plus
twice the kernel, plus the two exchange values, minus the losses of the record and of the minorant. -/
theorem pair_ineq (F : RecFacts P heads C i j h y σu σv m0 m1) {x : RecX} (hL : LayoutInj x.L)
    (hx : recordOk P h x = true) {mx : MinoX} (hLm : LayoutInj mx.L) (hmx : minoOk P h mx = true) :
    ((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
        - x.rho / 2 ^ x.E - (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip))
      ≤ 1 / (2 - 2 * C.t i j) := by
  have hA := rec_part F hL hx
  have hB := mino_part F hLm hmx
  linarith

end

end CAP.VR
