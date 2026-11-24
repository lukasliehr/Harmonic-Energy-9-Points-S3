module

public import CAP.VR.Sphere

/-!
# Virtual-root certificates: exact certificates

A certificate whose bound is attained has residuals zero. Its weights carry exact parts (`ExW`: terms
`A(X²) * ζ²` with natural coefficients of `A`, which are nonnegative at every real point), and it may be a
certificate for the function `den * f` with a natural number `den ≥ 1`, which stands for a common denominator
of its data. The checkers are `recordOkX`, `minoOkX`, `clsOk` and `boundOkX` (`CAP/VR/Kernel.lean`).

* `rec_partX`, `mino_partX`, `pair_ineqX`: the inequality of a pair, as in `CAP/VR/Pair.lean`;
* `energy_sum`: the sum over the pairs, from the inequalities of the pairs and of the labels;
* `energy_coordsX`: **the theorem of the schema S4 for an exact certificate, in coordinates**: `Bn / Bd ≤ E`;
* `energy_ge`: the same for nine points of the unit sphere of `ℝ⁴`.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open Finset

section

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ}

/-! ## The exact parts are nonnegative -/

theorem atomVal_nonneg (t : Atom) : 0 ≤ atomVal (realOps W L y) t := by
  show 0 ≤ (realOps W L y).dg t.delta t.dp t.cls t.wb t.d
    * (dot5 (realOps W L y) t.wz t.zc t.zp t.zn * dot5 (realOps W L y) t.wz t.zc t.zp t.zn)
  exact mul_nonneg (realOps_dg_nonneg y _ _ _ _ _) (mul_self_nonneg _)

theorem sqAtoms_nonneg : ∀ ats : List Atom, 0 ≤ sqAtoms (realOps W L y) ats
  | [] => by
    show (0 : ℝ) ≤ ((0 : ℕ) : ℝ)
    simp
  | t :: l => by
    show 0 ≤ atomVal (realOps W L y) t + sqAtoms (realOps W L y) l
    exact add_nonneg (atomVal_nonneg t) (sqAtoms_nonneg l)

/-- **The sum-of-squares side with exact parts is nonnegative** where its weights are. -/
theorem sosGoX_nonneg : ∀ (ws : List Weight) (ex : List ExW) (locs : List ℝ) (acc : ℝ), (∀ g ∈ locs, 0 ≤ g) → 0 ≤ acc →
    0 ≤ sosGoX (realOps W L y) ws ex locs acc
  | [], _, _, _, _, ha => ha
  | w :: l, ex, locs, acc, hl, ha => by
    rw [sosGoX_cons]
    refine sosGoX_nonneg l _ _ _ (fun g hg => hl g (tlA_mem hg)) ?_
    show 0 ≤ acc + hdA (realOps W L y) locs
      * (((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * sqBlocks (realOps W L y) w.blocks
        + ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats)
    exact add_nonneg ha (mul_nonneg (hdA_nonneg hl) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (sqBlocks_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (sqAtoms_nonneg _))))

end

/-! ## The inequality of a pair -/

theorem recValX_eq {α : Type} (o : Ops α) (P : Par) (h : RecH) (x : RecX) (ex : List ExW) :
    recValX o P h x ex = recValKX o P h x ex (i2p h) (i2q h) (clsM P h.c1) (clsM P h.c2) (recMT P h)
      (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1) (clsU o P h.c2 h.s2 (i2p h) (i2q h))
      (clsV o P h.c2 h.s2 (i2p h) (i2q h))
      (recT o P h (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1) (clsU o P h.c2 h.s2 (i2p h) (i2q h))
        (clsV o P h.c2 h.s2 (i2p h) (i2q h)))
      (clsR o (clsM P h.c1) (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1))
      (clsR o (clsM P h.c2) (clsU o P h.c2 h.s2 (i2p h) (i2q h)) (clsV o P h.c2 h.s2 (i2p h) (i2q h))) := rfl

theorem recValKX_eq {α : Type} (o : Ops α) (P : Par) (h : RecH) (x : RecX) (ex : List ExW) (i2p i2q m1 m2 mT : ℕ)
    (U1 V1 U2 V2 T R1 R2 : α) :
    recValKX o P h x ex i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
      = o.sub (recLhs o P h x i2p i2q mT T (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2))
        (cond (Nat.beq h.kind 1)
          (o.add (sosGoX o x.ws ex (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
              (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)) (o.nat 0))
            (o.smul (Nat.shiftLeft 1 x.aL) (o.mul (o.sub R2 R1) (dot5 o P.wP x.lex x.lp x.ln))))
          (sosGoX o x.ws ex (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2
            (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)) (o.nat 0))) := rfl

section

variable {P : Par} {heads : List RecH} {C : Conf} {i j : ℕ} {h : RecH} {y : Fin 5 → ℝ} {σu σv m0 m1 : ℝ}

/-- **The record of a pair**, for a record identity with exact parts. -/
theorem rec_partX (F : RecFacts P heads C i j h y σu σv m0 m1) {x : RecX} {ex : List ExW} (hL : LayoutInj x.L)
    (hx : recordOkX P h x ex = true) :
    ((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
        - x.rho / 2 ^ x.E
      ≤ poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP := by
  have hrec := recordOkX_sound hL hx F.cube
  obtain ⟨hpv, haC, haP, hks⟩ := scales_of (recordOkX_scales hx) (F.hm0 x.W x.L) (F.hm1 x.W x.L)
  have hR1 : clsR (realOps x.W x.L y) (clsM P h.c1) (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
      = 2 ^ (2 * clsM P h.c1) * C.R i := clsR_real _ F.su F.sv F.unit_i
  have hR2 : clsR (realOps x.W x.L y) (clsM P h.c2) (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j))
      = 2 ^ (2 * clsM P h.c2) * C.R j := clsR_real _ F.su F.sv F.unit_j
  have hH : recHv (realOps x.W x.L y) (clsM P h.c1) (clsM P h.c2) (recMT P h)
      (2 ^ clsM P h.c1 * (σu * C.u i)) (2 ^ clsM P h.c1 * (σv * C.v i))
      (2 ^ clsM P h.c2 * (σu * C.u j)) (2 ^ clsM P h.c2 * (σv * C.v j)) (2 ^ recMT P h * C.t i j)
      = 2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j := recHv_real _ _ _ F.su F.sv (t_eq C i j)
  rw [recValX_eq, F.U1, F.V1, F.U2, F.V2, F.T, hR1, hR2, recValKX_eq, hH] at hrec
  have hS := sosGoX_nonneg (W := x.W) (L := x.L) (y := y) x.ws ex _ ((0 : ℕ) : ℝ) (recLocs_nonneg F x.W x.L)
    (Nat.cast_nonneg 0)
  -- the term of the ideal vanishes
  have hval : |recLhs (realOps x.W x.L y) P h x (i2p h) (i2q h) (recMT P h) (2 ^ recMT P h * C.t i j)
        (2 ^ (recMT P h + clsM P h.c1 + clsM P h.c2) * C.Hh i j)
        ((2 ^ (2 * clsM P h.c1) * C.R i) * (2 ^ (2 * clsM P h.c2) * C.R j))
      - sosGoX (realOps x.W x.L y) x.ws ex (recLocs (realOps x.W x.L y) P h (i2p h) (i2q h) (clsM P h.c1) (clsM P h.c2)
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

/-- The value of the identity of a minorant with exact parts at the minorant point of a pair. -/
theorem minoValX_real (F : RecFacts P heads C i j h y σu σv m0 m1) (mx : MinoX) (ex : List ExW) (den : ℕ) :
    minoValX (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h mx ex den
      = den * 2 ^ mx.E - 2 ^ mx.aH * ((2 ^ minoMM h - 2 ^ minoMM h * C.t i j) * poly2 P.wP h.hex h.hp h.hn m0 m1)
        - sosGoX (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) mx.ws ex
          (minoLocs (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h (2 ^ minoMM h * C.t i j) (minoMM h)) 0 := by
  have hd : dotS (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P.wP 0 0 0 1 h.hex h.hp h.hn
      = poly2 P.wP h.hex h.hp h.hn m0 m1 :=
    dotS_real0 (at01 ![m0, m1, 0, 0, 0]) P.wP h.hex F.mcodes h.hp h.hn
  show ((Nat.shiftLeft den mx.E : ℕ) : ℝ)
    - ((Nat.shiftLeft 1 mx.aH : ℕ) : ℝ) * ((((Nat.shiftLeft 1 (minoMM h) : ℕ) : ℝ)
        - minoT (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) h)
      * dotS (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P.wP 0 0 0 1 h.hex h.hp h.hn)
    - sosGoX (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) mx.ws ex
        (minoLocs (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h (minoT (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) h) (minoMM h))
        ((0 : ℕ) : ℝ) = _
  rw [F.mT mx.W mx.L, hd, cast_shl, cast_shl1, cast_shl1, Nat.cast_zero]

theorem mcube_of (F : RecFacts P heads C i j h y σu σv m0 m1) : ∀ k, |(![m0, m1, 0, 0, 0] : Fin 5 → ℝ) k| ≤ 1 := by
  intro k
  fin_cases k
  · exact F.mcube.1
  · exact F.mcube.2
  · simp
  · simp
  · simp

/-- **The minorant of a pair**, for a minorant identity of the function `den * f` with exact parts. -/
theorem mino_partX (F : RecFacts P heads C i j h y σu σv m0 m1) {mx : MinoX} {ex : List ExW} {den : ℕ}
    (hLm : LayoutInj mx.L) (hmx : minoOkX P h mx ex den = true) :
    poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP
        - (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip))
      ≤ den / (2 - 2 * C.t i j) := by
  have hmin := minoOkX_sound hLm hmx (mcube_of F)
  have hmx' : (Nat.beq (Nat.add (Nat.add mx.aH (minoMM h)) P.sP) (Nat.succ mx.E) && exwOk mx.W mx.L ex
      && runOk mx.L mx.W mx.wr mx.rho mx.ws (minoValX (pairOps mx.W mx.L) P h mx ex den) (minoValX (absOps mx.L) P h mx ex den)
        (minoValX degOps P h mx ex den) (minoValX (pdegOps mx.L.pm) P h mx ex den) (minoValX (posOps mx.L) P h mx ex den)
        (minoValX (clsOps mx.L.pv) P h mx ex den)) = true := hmx
  simp only [Bool.and_eq_true] at hmx'
  have hsc : mx.aH + minoMM h + P.sP = mx.E + 1 := Nat.eq_of_beq_eq_true hmx'.1.1
  have hS := sosGoX_nonneg (W := mx.W) (L := mx.L) (y := ![m0, m1, 0, 0, 0]) mx.ws ex _ 0 (F.mlocs mx.W mx.L) le_rfl
  rw [minoValX_real F] at hmin
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
  -- with `q = pv / 2 ^ sP`: `-rho ≤ 2 ^ E * (den - 2 * (1 - t) * q)`
  have hq : -(mx.rho : ℝ) ≤ 2 ^ mx.E * (den - 2 * (1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
    have e : (2 : ℝ) ^ mx.aH * ((2 ^ minoMM h - 2 ^ minoMM h * C.t i j) * poly2 P.wP h.hex h.hp h.hn m0 m1)
        = (2 ^ mx.aH * 2 ^ minoMM h * 2 ^ P.sP) * ((1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
      field_simp
    rw [e, hE1] at hlow
    linarith
  have h1 : poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP
      ≤ ((den : ℝ) * 2 ^ mx.E + mx.rho) / (2 * (1 - C.t i j) * 2 ^ mx.E) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2 : ((den : ℝ) * 2 ^ mx.E + mx.rho) / (2 * (1 - C.t i j) * 2 ^ mx.E)
      = den / (2 - 2 * C.t i j) + mx.rho / (2 ^ (mx.E + 1) * (1 - C.t i j)) := by
    have hne : (2 : ℝ) - 2 * C.t i j ≠ 0 := by linarith
    have hne' : (1 : ℝ) - C.t i j ≠ 0 := by linarith
    have hE0 : (2 : ℝ) ^ mx.E ≠ 0 := by positivity
    rw [pow_succ, div_add_div _ _ hne (mul_ne_zero (mul_ne_zero hE0 two_ne_zero) hne'),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hne') hE0)
        (mul_ne_zero hne (mul_ne_zero (mul_ne_zero hE0 two_ne_zero) hne'))]
    ring
  have h3 : (mx.rho : ℝ) / (2 ^ (mx.E + 1) * (1 - C.t i j))
      ≤ (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hgd (mul_nonneg hρ (by positivity : (0 : ℝ) ≤ 2 ^ (mx.E + 1)))
    linarith
  linarith

/-- **The inequality of a pair** for the identities with exact parts of the function `den * f`. -/
theorem pair_ineqX (F : RecFacts P heads C i j h y σu σv m0 m1) {x : RecX} {ex : List ExW} (hL : LayoutInj x.L)
    (hx : recordOkX P h x ex = true) {mx : MinoX} {mex : List ExW} {den : ℕ} (hLm : LayoutInj mx.L)
    (hmx : minoOkX P h mx mex den = true) :
    ((h.cp : ℝ) - h.cn) / 2 ^ P.sP + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP
        - x.rho / 2 ^ x.E - (mx.rho * h.hid) / (2 ^ (mx.E + 1) * ((h.hid : ℝ) + h.hin - h.hip))
      ≤ den / (2 - 2 * C.t i j) := by
  have hA := rec_partX F hL hx
  have hB := mino_partX F hLm hmx
  linarith

end

/-! ## The sum over the pairs -/

/-- **The sum over the pairs**, from the inequalities of the pairs and of the labels: the sum of the lower bounds
is at most the sum of the values `f i j`. -/
theorem energy_sum (P : Par) (heads : List RecH) (C : Conf) (cpair f : ℕ → ℕ → ℝ) (clab : ℕ → ℝ)
    (hpair : ∀ j ∈ range 9, ∀ i ∈ range j,
      cpair i j + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP ≤ f i j)
    (hlabel : ∀ l ∈ range 9,
      Kl P C l l + clab l ≤ (∑ o ∈ range 9, if o = l then 0 else piN P heads C l o) / 2 ^ P.sP) :
    (∑ j ∈ range 9, ∑ i ∈ range j, cpair i j) + ∑ l ∈ range 9, clab l ≤ ∑ j ∈ range 9, ∑ i ∈ range j, f i j := by
  have h1 := Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hpair j hj i hi
  have h2 : ∑ j ∈ range 9, ∑ i ∈ range j, (cpair i j + 2 * Kl P C i j
        + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP)
      = (∑ j ∈ range 9, ∑ i ∈ range j, cpair i j)
        + (∑ j ∈ range 9, ∑ i ∈ range j, (Kl P C i j + Kl P C j i))
        + (∑ j ∈ range 9, ∑ i ∈ range j, (piN P heads C i j + piN P heads C j i)) / 2 ^ P.sP := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Kl_comm P C j i]
    ring
  have e1 := sum_pairs (fun i j => Kl P C i j) 9
  have e2 := sum_pairs (fun i j => piN P heads C i j) 9
  rw [h2, e1, e2] at h1
  have h3 : ∑ l ∈ range 9, (∑ o ∈ range 9, if o = l then 0 else Kl P C l o)
      = ∑ l ∈ range 9, ∑ o ∈ range 9, Kl P C l o - ∑ l ∈ range 9, Kl P C l l := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l hl => sum_ne _ (Finset.mem_range.1 hl)
  have h5 : ∑ l ∈ range 9, (Kl P C l l + clab l)
      ≤ (∑ l ∈ range 9, ∑ o ∈ range 9, if o = l then 0 else piN P heads C l o) / 2 ^ P.sP := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum hlabel
  rw [Finset.sum_add_distrib] at h5
  have h6 := Kl_psd P C (range 9)
  rw [h3] at h1
  linarith

/-! ## The theorem of the schema for an exact certificate -/

section

variable {P : Par} {heads : List RecH} {C : Conf}

/-- The content of the check `boundOkX`. -/
theorem boundOkX_real {den Bn Bd : ℕ} (hb : boundOkX P heads den Bn Bd = true) :
    1 ≤ den ∧ 1 ≤ Bd
      ∧ (Bn : ℝ) * den * 2 ^ P.sP + Bd * (∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cn : ℝ))
        ≤ Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cp : ℝ)) + ∑ l ∈ range 9, (guardN P l : ℝ)) := by
  have hb' : (Nat.ble 1 den && Nat.ble 1 Bd
      && Nat.ble
        (Nat.add (Nat.shiftLeft (Nat.mul Bn den) P.sP)
          (Nat.mul Bd (sumN (fun j => sumN (fun i => (hdOf P heads i j).cn) j) 9)))
        (Nat.mul Bd (Nat.add (sumN (fun j => sumN (fun i => (hdOf P heads i j).cp) j) 9) (sumN (guardN P) 9))))
      = true := hb
  simp only [Bool.and_eq_true] at hb'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb'
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, ?_⟩
  have e1 : sumN (fun j => sumN (fun i => (hdOf P heads i j).cn) j) 9
      = ∑ j ∈ range 9, ∑ i ∈ range j, (hdOf P heads i j).cn := by
    rw [sumN_eq]
    exact Finset.sum_congr rfl fun j _ => sumN_eq _ _
  have e2 : sumN (fun j => sumN (fun i => (hdOf P heads i j).cp) j) 9
      = ∑ j ∈ range 9, ∑ i ∈ range j, (hdOf P heads i j).cp := by
    rw [sumN_eq]
    exact Finset.sum_congr rfl fun j _ => sumN_eq _ _
  have h0 : Bn * den * 2 ^ P.sP + Bd * (∑ j ∈ range 9, ∑ i ∈ range j, (hdOf P heads i j).cn)
      ≤ Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, (hdOf P heads i j).cp) + ∑ l ∈ range 9, guardN P l) := by
    have h := Nat.le_of_ble_eq_true h3
    rw [e1, e2, sumN_eq, show Nat.shiftLeft (Nat.mul Bn den) P.sP = Bn * den * 2 ^ P.sP from Nat.shiftLeft_eq _ _] at h
    exact h
  have hR := (Nat.cast_le (α := ℝ)).2 h0
  push_cast at hR
  exact hR

/-- **The checked identities of an exact certificate** for the function `den * f`: every record type has a checked
record identity and a checked minorant identity, every label has a checked identity, all with the residual zero, in
layouts that are injective on the admissible monomials. -/
structure CheckedX (P : Par) (heads : List RecH) (den : ℕ) : Prop where
  recs : ∀ k, k < lenH heads → ∃ (x : RecX) (ex : List ExW), LayoutInj x.L ∧ recordOkX P (nthH heads k) x ex = true
    ∧ x.rho = 0
  minos : ∀ k, k < lenH heads → ∃ (x : MinoX) (ex : List ExW), LayoutInj x.L ∧ minoOkX P (nthH heads k) x ex den = true
    ∧ x.rho = 0
  clss : ∀ l, l < 9 → ∃ x : ClsX, LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l ∧ x.rho = 0

theorem pair_index_lt (hlab : labelsOk P heads = true) {i j : ℕ} (hij : i < j) (hj : j < 9) :
    nth P.rt (pairIndex i j) < lenH heads := by
  have hp := (labOk_of hlab).pair i j hij hj
  unfold pairOk at hp
  rw [Bool.and_eq_true] at hp
  exact lt_of_blt hp.1

/-- The inequality of every pair of labels, for an exact certificate. -/
theorem pairX (hlab : labelsOk P heads = true) {den : ℕ} (hck : CheckedX P heads den) (hin : InPiece P heads C)
    {i j : ℕ} (hij : i < j) (hj : j < 9) :
    (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP + 2 * Kl P C i j
        + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP ≤ den / (2 - 2 * C.t i j) := by
  obtain ⟨y, σu, σv, m0, m1, Fa⟩ := rec_facts hlab hin hij hj
  obtain ⟨x, ex, hxL, hxok, hxr⟩ := hck.recs _ (pair_index_lt hlab hij hj)
  obtain ⟨mx, mex, hmL, hmok, hmr⟩ := hck.minos _ (pair_index_lt hlab hij hj)
  have h1 := pair_ineqX Fa hxL hxok hmL hmok
  rw [hxr, hmr] at h1
  simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero] at h1
  exact h1

/-- The inequality of every label, for an exact certificate. -/
theorem labelX (hlab : labelsOk P heads = true) {den : ℕ} (hck : CheckedX P heads den) (hin : InPiece P heads C)
    {l : ℕ} (hl : l < 9) :
    Kl P C l l + (guardN P l : ℝ) / 2 ^ P.sP
      ≤ (∑ o ∈ range 9, if o = l then 0 else piN P heads C l o) / 2 ^ P.sP := by
  obtain ⟨x, hxL, hxok, rfl, hxr⟩ := hck.clss l hl
  have h1 := label_ineq hlab hin hxL hxok
  rw [hxr] at h1
  simp only [Nat.cast_zero, zero_div, sub_zero] at h1
  exact h1

/-- **The theorem of the schema S4 for an exact certificate, in coordinates.** A configuration of the piece of a
checked exact certificate has an energy of at least the bound `Bn / Bd` of the certificate. -/
theorem energy_coordsX {den Bn Bd : ℕ} (hlab : labelsOk P heads = true) (hck : CheckedX P heads den)
    (hb : boundOkX P heads den Bn Bd = true) (hin : InPiece P heads C) :
    (Bn : ℝ) / Bd ≤ ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) := by
  obtain ⟨hden, hBd, hR⟩ := boundOkX_real hb
  have hsum := energy_sum P heads C
    (fun i j => (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP)
    (fun i j => den / (2 - 2 * C.t i j)) (fun l => (guardN P l : ℝ) / 2 ^ P.sP)
    (fun j hj i hi => pairX hlab hck hin (Finset.mem_range.1 hi) (Finset.mem_range.1 hj))
    (fun l hl => labelX hlab hck hin (Finset.mem_range.1 hl))
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hBdR : (0 : ℝ) < Bd := by exact_mod_cast hBd
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  have e1 : ∑ j ∈ range 9, ∑ i ∈ range j, (den : ℝ) / (2 - 2 * C.t i j)
      = den * ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : (∑ j ∈ range 9, ∑ i ∈ range j, (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP)
      + ∑ l ∈ range 9, (guardN P l : ℝ) / 2 ^ P.sP
      = (((∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cp : ℝ)) + ∑ l ∈ range 9, (guardN P l : ℝ))
        - ∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cn : ℝ)) / 2 ^ P.sP := by
    simp only [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e1, e2] at hsum
  rw [div_le_iff₀ hBdR]
  rw [div_le_iff₀ hSP] at hsum
  have h4 := mul_le_mul_of_nonneg_left hsum hBdR.le
  have h5 : (Bn : ℝ) * (den * 2 ^ P.sP)
      ≤ (∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j)) * Bd * (den * 2 ^ P.sP) := by
    have e3 : (Bd : ℝ) * ((den * ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j)) * 2 ^ P.sP)
        = (∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j)) * Bd * (den * 2 ^ P.sP) := by ring
    rw [e3] at h4
    linarith
  exact le_of_mul_le_mul_right h5 (mul_pos hdenR hSP)

end

/-! ## Points of the sphere -/

section

variable {P : Par} {heads : List RecH}

/-- **The theorem of the schema S4 for an exact certificate.** If the labels, the identities and the bound of an
exact virtual-root certificate are checked, then the energy of every configuration of its piece is at least
`Bn / Bd`. -/
theorem energy_ge {den Bn Bd : ℕ} (hlab : labelsOk P heads = true) (hck : CheckedX P heads den)
    (hb : boundOkX P heads den Bn Bd = true) {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)}
    (hin : InPieceS P heads x e f) :
    (Bn : ℝ) / Bd ≤ ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 := by
  have hv : Orthonormal ℝ (({0, 1} : Set (Fin 4)).domRestrict ![e, f, 0, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · simp [Set.domRestrict, hin.eu]
    · simp [Set.domRestrict, hin.ef]
    · have : inner ℝ f e = 0 := by rw [real_inner_comm, hin.ef]
      simp [Set.domRestrict, this]
    · simp [Set.domRestrict, hin.fu]
  obtain ⟨b, hb'⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have h0 : b 0 = e := hb' 0 (by simp)
  have h1 : b 1 = f := hb' 1 (by simp)
  obtain ⟨hI, hT⟩ := inPiece_of hin b h0 h1
  have h := energy_coordsX hlab hck hb hI
  rw [← sum_fin_pairs 9 (fun i j => 1 / (2 - 2 * (confOf x e f (b 2) (b 3)).t i j))] at h
  refine le_of_le_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hT, pt_coe, pt_coe, norm_sub_sq_real, hin.unit, hin.unit]
  congr 1
  ring

/-! ## The checked identities from lists -/

/-- The record identities with exact parts of a list of record types. -/
def RecsOkX (P : Par) : List RecH → List RecX → List (List ExW) → Prop
  | [], _, _ => True
  | h :: hs, x :: xs, e :: es => (LayoutInj x.L ∧ recordOkX P h x e = true ∧ x.rho = 0) ∧ RecsOkX P hs xs es
  | _ :: _, _, _ => False

/-- The minorant identities with exact parts of a list of record types. -/
def MinosOkX (P : Par) (den : ℕ) : List RecH → List MinoX → List (List ExW) → Prop
  | [], _, _ => True
  | h :: hs, x :: xs, e :: es => (LayoutInj x.L ∧ minoOkX P h x e den = true ∧ x.rho = 0) ∧ MinosOkX P den hs xs es
  | _ :: _, _, _ => False

/-- The identities of the labels `l, l + 1, …`, with the residual zero. -/
def ClssOkX (P : Par) (heads : List RecH) : ℕ → List ClsX → Prop
  | _, [] => True
  | l, x :: xs => (LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l ∧ x.rho = 0) ∧ ClssOkX P heads (l + 1) xs

theorem recsOkX_nth : ∀ (hs : List RecH) (xs : List RecX) (es : List (List ExW)), RecsOkX P hs xs es → ∀ k, k < lenH hs →
    ∃ (x : RecX) (ex : List ExW), LayoutInj x.L ∧ recordOkX P (nthH hs k) x ex = true ∧ x.rho = 0
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | _ :: _, _ :: _, [], hf, _, _ => False.elim hf
  | _ :: _, x :: _, e :: _, hr, 0, _ => ⟨x, e, hr.1⟩
  | _ :: hs, _ :: xs, _ :: es, hr, k + 1, hk => recsOkX_nth hs xs es hr.2 k (Nat.lt_of_succ_lt_succ hk)

theorem minosOkX_nth {den : ℕ} : ∀ (hs : List RecH) (xs : List MinoX) (es : List (List ExW)), MinosOkX P den hs xs es →
    ∀ k, k < lenH hs → ∃ (x : MinoX) (ex : List ExW), LayoutInj x.L ∧ minoOkX P (nthH hs k) x ex den = true ∧ x.rho = 0
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | _ :: _, _ :: _, [], hf, _, _ => False.elim hf
  | _ :: _, x :: _, e :: _, hr, 0, _ => ⟨x, e, hr.1⟩
  | _ :: hs, _ :: xs, _ :: es, hr, k + 1, hk => minosOkX_nth hs xs es hr.2 k (Nat.lt_of_succ_lt_succ hk)

theorem clssOkX_nth : ∀ (cs : List ClsX) (l0 : ℕ), ClssOkX P heads l0 cs → ∀ k, k < cs.length →
    ∃ x : ClsX, LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l0 + k ∧ x.rho = 0
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | x :: _, _, hr, 0, _ => ⟨x, hr.1⟩
  | _ :: cs, l0, hr, k + 1, hk => by
    obtain ⟨x, h1, h2, h3, h4⟩ := clssOkX_nth cs (l0 + 1) hr.2 k (Nat.lt_of_succ_lt_succ hk)
    exact ⟨x, h1, h2, by rw [h3]; omega, h4⟩

/-- **The checked identities of an exact certificate**, from the lists of its records, minorants and labels. -/
theorem checkedX_of {den : ℕ} {xs : List RecX} {es : List (List ExW)} {ms : List MinoX} {mes : List (List ExW)}
    {cs : List ClsX} (h1 : RecsOkX P heads xs es) (h2 : MinosOkX P den heads ms mes) (h3 : ClssOkX P heads 0 cs)
    (h9 : cs.length = 9) : CheckedX P heads den where
  recs := recsOkX_nth heads xs es h1
  minos := minosOkX_nth heads ms mes h2
  clss := fun l hl => by
    obtain ⟨x, a, b, c, d⟩ := clssOkX_nth cs 0 h3 l (by omega)
    exact ⟨x, a, b, by rw [c]; omega, d⟩

end

end CAP.VR
