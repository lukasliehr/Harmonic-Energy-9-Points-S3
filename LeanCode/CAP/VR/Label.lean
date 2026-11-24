module

public import CAP.VR.Kinds

/-!
# Virtual-root certificates: the inequality of a label

For a label `l` of a configuration of the piece, the checked identity of the label (`clsOk`) gives

  `K(l, l) + (guard term) - (loss of the identity) ≤ ∑ o ≠ l, π(l; o)`

(`label_ineq`): the sum of the exchange values of `l` towards the other labels is at least the kernel at
`(l, l)` plus the term `lamL * lowN` of the lower guard of its class.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open Finset

variable {W : ℕ} {L : Lay} {P : Par} {heads : List RecH} {C : Conf}

/-! ## The exchange terms -/

theorem nthH_ge : ∀ (l : List RecH) (k : ℕ), lenH l ≤ k → nthH l k = RecH.none
  | [], _, _ => rfl
  | _ :: l, 0, h => absurd h (Nat.not_succ_le_zero (lenH l))
  | _ :: l, k + 1, h => nthH_ge l k (Nat.le_of_succ_le_succ h)

/-- The exponents of the exchange polynomials of every record type are below `16`. -/
theorem nthH_codes (lab : LabOk P heads) (k : ℕ) :
    (∀ c ∈ (nthH heads k).p1ex, c < 256) ∧ (∀ c ∈ (nthH heads k).p2ex, c < 256) := by
  by_cases hk : k < lenH heads
  · obtain ⟨hf, -⟩ := headOk_real (lab.head _ (nthH_mem heads k hk))
    obtain ⟨h1, h2, -, -⟩ := formOk_real hf
    exact ⟨h1, h2⟩
  · rw [nthH_ge heads k (by omega)]
    exact ⟨fun c hc => absurd (show c ∈ ([] : List ℕ) from hc) List.not_mem_nil,
      fun c hc => absurd (show c ∈ ([] : List ℕ) from hc) List.not_mem_nil⟩

theorem piTerm_real (lab : LabOk P heads) {l ot : ℕ} {y : Fin 5 → ℝ} (h0 : y 0 = cp P C l) (h1 : y 1 = cq P C l)
    (W : ℕ) (L : Lay) : piTerm (realOps W L y) P heads l ot = piN P heads C l ot := by
  obtain ⟨hc1, hc2⟩ : (∀ c ∈ (headOf P heads l ot).p1ex, c < 256) ∧ (∀ c ∈ (headOf P heads l ot).p2ex, c < 256) :=
    nthH_codes lab (nth P.rt (cond (Nat.blt l ot) (pairIndex l ot) (pairIndex ot l)))
  unfold piTerm piN
  by_cases h : l < ot
  · have hb : Nat.blt l ot = true := by
      rw [Nat.blt_eq]
      exact h
    rw [hb, if_pos h]
    show dotS (realOps W L y) P.wP (flipP l ot) (flipQ l ot) 0 1 (headOf P heads l ot).p1ex (headOf P heads l ot).p1p
      (headOf P heads l ot).p1n = _
    rw [dotS_real (at01 y) (flipP_lt l ot) (flipQ_lt l ot) P.wP _ hc1, h0, h1]
    rfl
  · have hb : Nat.blt l ot = false := by
      cases hbb : Nat.blt l ot
      · rfl
      · exact absurd (lt_of_blt hbb) h
    rw [hb, if_neg h]
    show dotS (realOps W L y) P.wP (flipP l ot) (flipQ l ot) 0 1 (headOf P heads l ot).p2ex (headOf P heads l ot).p2p
      (headOf P heads l ot).p2n = _
    rw [dotS_real (at01 y) (flipP_lt l ot) (flipQ_lt l ot) P.wP _ hc2, h0, h1]
    rfl

/-! ## The coordinates of a label -/

theorem label_UV (lab : LabOk P heads) (hin : InPiece P heads C) {l : ℕ} (hl : l < 9) {y : Fin 5 → ℝ}
    (h0 : y 0 = cp P C l) (h1 : y 1 = cq P C l) (W : ℕ) (L : Lay) :
    clsU (realOps W L y) P (nth P.dcls l) (nth P.dsg l) 0 1 = 2 ^ clsM P (nth P.dcls l) * (1 * C.u l)
      ∧ clsV (realOps W L y) P (nth P.dcls l) (nth P.dsg l) 0 1 = 2 ^ clsM P (nth P.dcls l) * (1 * C.v l) := by
  have hip : var (realOps W L y) 0 = cp P C l := by rw [var0, h0]
  have hiq : var (realOps W L y) 1 = 1 * cq P C l := by rw [var1, h1, one_mul]
  have hip' : var (realOps W L y) 0 = 1 * cp P C l := by rw [var0, h0, one_mul]
  obtain rfl | rfl | rfl | rfl | h4 : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ 4 ≤ l := by omega
  · have E := endA (W := W) (L := L) (y := y) (l := 0) (by norm_num) (hin.pairA 0 (by norm_num)) (τ := 1)
      (by norm_num) hip hiq 0
    rw [lab.c0, lab.s0]
    refine ⟨?_, E.2.1⟩
    rw [E.1, sgA0, eps0]
    ring
  · have E := endA (W := W) (L := L) (y := y) (l := 1) (by norm_num) (hin.pairA 1 (by norm_num)) (τ := 1)
      (by norm_num) hip hiq 1
    rw [lab.c1, lab.s1]
    refine ⟨?_, E.2.1⟩
    rw [E.1, sgA1, eps1]
    ring
  · have E := endB (W := W) (L := L) (y := y) (l := 2) (le_refl 2) (by norm_num)
      (hin.pairB 2 (le_refl 2) (by norm_num)) (τ := 1) (by norm_num) hip hiq 0
    rw [lab.c2, lab.s2]
    refine ⟨E.1, ?_⟩
    rw [E.2.1, sgA0, eps2]
    ring
  · have E := endB (W := W) (L := L) (y := y) (l := 3) (by norm_num) (by norm_num)
      (hin.pairB 3 (by norm_num) (by norm_num)) (τ := 1) (by norm_num) hip hiq 1
    rw [lab.c3, lab.s3]
    refine ⟨E.1, ?_⟩
    rw [E.2.1, sgA1, eps3]
    ring
  · obtain ⟨r1, r2, r3, r4⟩ := hin.ring l h4 hl
    have E := endR (W := W) (L := L) (y := y) (l := l) (cls := nth P.dcls l) h4 (lab.ring l h4 hl) r1 r2 r3 r4
      (τp := 1) (τq := 1) (by norm_num) (by norm_num) hip' hiq (nth P.dsg l)
    exact ⟨E.1, E.2.1⟩

/-! ## The guards -/

/-- The term of the lower guard of the class of a label, in the unit `2 ^ -sP`. -/
noncomputable def guardN (P : Par) (l : ℕ) : ℕ :=
  cond (Nat.ble 2 (nth P.dcls l))
    (Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2))) 0

theorem clsLam_ge (lab : LabOk P heads) (hin : InPiece P heads C) {l : ℕ} (hl : l < 9) {y : Fin 5 → ℝ}
    (h0 : y 0 = cp P C l) (h1 : y 1 = cq P C l) (W : ℕ) (L : Lay) :
    (guardN P l : ℝ) ≤ clsLam (realOps W L y) P (nth P.dcls l) := by
  unfold guardN clsLam
  by_cases h4 : 4 ≤ l
  · have hc := lab.ring l h4 hl
    have hb : Nat.blt (nth P.dcls l) 2 = false := by
      cases hbb : Nat.blt (nth P.dcls l) 2
      · rfl
      · exact absurd (lt_of_blt hbb) (by omega)
    rw [Nat.ble_eq_true_of_le hc, hb]
    obtain ⟨_, _, r3, r4⟩ := hin.ring l h4 hl
    have hcp : cp P C l = C.u l := by
      unfold cp
      rw [if_neg (by omega), if_neg (by omega)]
    have hcq : cq P C l = C.v l := by
      unfold cq
      rw [if_neg (by omega), if_neg (by omega)]
    show ((Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2)) : ℕ) : ℝ)
      ≤ (P.lamG : ℝ) * (((var (realOps W L y) 0 * var (realOps W L y) 0 + var (realOps W L y) 1 * var (realOps W L y) 1)
            * (var (realOps W L y) 0 * var (realOps W L y) 0 + var (realOps W L y) 1 * var (realOps W L y) 1))
          * ((P.Gn : ℝ) - (P.Gd : ℝ) * (var (realOps W L y) 0 * var (realOps W L y) 0
            + var (realOps W L y) 1 * var (realOps W L y) 1)))
        + ((Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowD (Nat.sub (nth P.dcls l) 2)) : ℕ) : ℝ)
          * (var (realOps W L y) 0 * var (realOps W L y) 0 + var (realOps W L y) 1 * var (realOps W L y) 1)
    rw [var0, var1, h0, h1, hcp, hcq]
    have e1 : ((Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2)) : ℕ) : ℝ)
        = (nth P.lamL (nth P.dcls l - 2) : ℝ) * (nth P.lowN (nth P.dcls l - 2) : ℝ) := Nat.cast_mul _ _
    have e2 : ((Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowD (Nat.sub (nth P.dcls l) 2)) : ℕ) : ℝ)
        = (nth P.lamL (nth P.dcls l - 2) : ℝ) * (nth P.lowD (nth P.dcls l - 2) : ℝ) := Nat.cast_mul _ _
    rw [e1, e2]
    have hG : (0 : ℝ) ≤ (P.lamG : ℝ) * ((C.u l * C.u l + C.v l * C.v l) * (C.u l * C.u l + C.v l * C.v l)
        * ((P.Gn : ℝ) - (P.Gd : ℝ) * (C.u l * C.u l + C.v l * C.v l))) := by
      refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_self_nonneg _) ?_)
      nlinarith
    have hLm : (0 : ℝ) ≤ (nth P.lamL (nth P.dcls l - 2) : ℝ) := Nat.cast_nonneg _
    have hLw := mul_le_mul_of_nonneg_left r4 hLm
    nlinarith
  · have hc : nth P.dcls l < 2 := by
      obtain rfl | rfl | rfl | rfl : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 := by omega
      · rw [lab.c0]
        norm_num
      · rw [lab.c1]
        norm_num
      · rw [lab.c2]
        norm_num
      · rw [lab.c3]
        norm_num
    have hb : Nat.blt (nth P.dcls l) 2 = true := by
      rw [Nat.blt_eq]
      exact hc
    rw [ble_false (by omega : nth P.dcls l < 2), hb]
    show ((0 : ℕ) : ℝ) ≤ ((0 : ℕ) : ℝ)
    exact le_refl _

/-! ## The inequality of a label -/

theorem cube_label (lab : LabOk P heads) (hin : InPiece P heads C) {l : ℕ} (hl : l < 9) :
    ∀ k, |(![cp P C l, cq P C l, 0, 0, 0] : Fin 5 → ℝ) k| ≤ 1 := by
  intro k
  fin_cases k
  · exact (cp_abs lab hin hl).1
  · exact (cp_abs lab hin hl).2
  · simp
  · simp
  · simp

/-- **The inequality of a label.** -/
theorem label_ineq (hlab : labelsOk P heads = true) (hin : InPiece P heads C) {x : ClsX} (hL : LayoutInj x.L)
    (hx : clsOk P heads x = true) :
    Kl P C x.label x.label + (guardN P x.label : ℝ) / 2 ^ P.sP - x.rho / 2 ^ x.E
      ≤ (∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o) / 2 ^ P.sP := by
  have lab := labOk_of hlab
  have hx' : (Nat.beq (Nat.add x.aP P.sP) x.E && Nat.beq (Nat.add x.aL P.sP) x.E && Nat.blt x.label 9
      && cScalesGo (nth P.dcls x.label) (clsM P (nth P.dcls x.label)) x.E P.kblocks x.aK P.sK 0
      && runOk x.L x.W x.wr x.rho [] (clsVal (pairOps x.W x.L) P heads x) (clsVal (absOps x.L) P heads x)
        (clsVal degOps P heads x) (clsVal (pdegOps x.L.pm) P heads x) (clsVal (posOps x.L) P heads x)
        (clsVal (clsOps x.L.pv) P heads x)) = true := hx
  simp only [Bool.and_eq_true] at hx'
  obtain ⟨⟨⟨⟨a, b⟩, hl9⟩, hsc⟩, _⟩ := hx'
  have haP : x.aP + P.sP = x.E := Nat.eq_of_beq_eq_true a
  have haL : x.aL + P.sP = x.E := Nat.eq_of_beq_eq_true b
  have hl : x.label < 9 := lt_of_blt hl9
  have hval := clsOk_sound hL hx (cube_label lab hin hl)
  obtain ⟨hU, hV⟩ := label_UV lab hin hl (y := ![cp P C x.label, cq P C x.label, 0, 0, 0]) rfl rfl x.W x.L
  have hR : clsR (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) (clsM P (nth P.dcls x.label))
      (2 ^ clsM P (nth P.dcls x.label) * (1 * C.u x.label)) (2 ^ clsM P (nth P.dcls x.label) * (1 * C.v x.label))
      = 2 ^ (2 * clsM P (nth P.dcls x.label)) * C.R x.label :=
    clsR_real _ (by norm_num) (by norm_num) (hin.unit x.label hl)
  -- the exchange terms
  have hPhi : clsPhiGo (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P heads x.label 9 ((0 : ℕ) : ℝ)
      = ∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o := by
    rw [clsPhiGo_real, Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : o = x.label
    · rw [if_pos ho, if_pos ho]
    · rw [if_neg ho, if_neg ho]
      exact piTerm_real lab rfl rfl x.W x.L
  -- the kernel term
  have hat : At (![cp P C x.label, cq P C x.label, 0, 0, 0] : Fin 5 → ℝ) 0 1 ((-1) ^ 0 * cp P C x.label)
      ((-1) ^ 0 * cq P C x.label) := by
    have h := at01 (![cp P C x.label, cq P C x.label, 0, 0, 0] : Fin 5 → ℝ)
    have e0 : (![cp P C x.label, cq P C x.label, 0, 0, 0] : Fin 5 → ℝ) 0 = (-1) ^ 0 * cp P C x.label := by
      show cp P C x.label = _
      ring
    have e1 : (![cp P C x.label, cq P C x.label, 0, 0, 0] : Fin 5 → ℝ) 1 = (-1) ^ 0 * cq P C x.label := by
      show cq P C x.label = _
      ring
    rw [e0, e1] at h
    exact h
  have hinner := inner_cov (y := ![cp P C x.label, cq P C x.label, 0, 0, 0]) (i := x.label) (j := x.label)
    (c1 := nth P.dcls x.label) (s1 := nth P.dsg x.label) (c2 := nth P.dcls x.label) (s2 := nth P.dsg x.label)
    (tp1 := 0) (tq1 := 0) (tp2 := 0) (tq2 := 0) lab.kb rfl rfl hat hat (fun _ => rfl) (fun _ => rfl)
    (fun blk _ _ => by
      unfold chiF
      simp) x.W x.L
  have hD : clsDeltaGo (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) (nth P.dcls x.label)
      (nth P.dsg x.label) (2 ^ (2 * clsM P (nth P.dcls x.label)) * C.R x.label) P.kblocks x.aK ((1 : ℕ) : ℝ)
      ((0 : ℕ) : ℝ) = 2 ^ x.E * Kl P C x.label x.label := by
    rw [clsDeltaGo_real (r := C.R x.label) (m := clsM P (nth P.dcls x.label)) (E := x.E) rfl P.kblocks x.aK P.sK 0
      ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ) hsc (by simp), Nat.cast_zero, zero_add,
      kernR_congr (fun k => (C.Qr_self x.label k).symm) P.kblocks hinner P.sK 0]
    rfl
  have hLam := clsLam_ge lab hin hl (y := ![cp P C x.label, cq P C x.label, 0, 0, 0]) rfl rfl x.W x.L
  -- the value of the identity
  have hv : clsVal (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P heads x
      = 2 ^ x.aP * (∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o)
        - (2 ^ x.E * Kl P C x.label x.label
          + 2 ^ x.aL * clsLam (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P (nth P.dcls x.label)) := by
    show ((Nat.shiftLeft 1 x.aP : ℕ) : ℝ)
        * clsPhiGo (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P heads x.label 9 ((0 : ℕ) : ℝ)
      - (clsDeltaGo (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) (nth P.dcls x.label)
            (nth P.dsg x.label)
            (clsR (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) (clsM P (nth P.dcls x.label))
              (clsU (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P (nth P.dcls x.label)
                (nth P.dsg x.label) 0 1)
              (clsV (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P (nth P.dcls x.label)
                (nth P.dsg x.label) 0 1))
            P.kblocks x.aK ((1 : ℕ) : ℝ) ((0 : ℕ) : ℝ)
        + ((Nat.shiftLeft 1 x.aL : ℕ) : ℝ)
          * clsLam (realOps x.W x.L ![cp P C x.label, cq P C x.label, 0, 0, 0]) P (nth P.dcls x.label)) = _
    rw [hPhi, hU, hV, hR, hD, cast_shl1, cast_shl1]
  rw [hv] at hval
  have hlow := (abs_le.1 hval).1
  -- the arithmetic of the scales
  have hE : (2 : ℝ) ^ x.E = 2 ^ x.aP * 2 ^ P.sP := by rw [← haP, pow_add]
  have hLP : x.aL = x.aP := by omega
  rw [hLP, hE] at hlow
  rw [hE]
  have hA : (0 : ℝ) < 2 ^ x.aP := by positivity
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  have hLam' := mul_le_mul_of_nonneg_left hLam hA.le
  have key : (Kl P C x.label x.label + (guardN P x.label : ℝ) / 2 ^ P.sP - x.rho / (2 ^ x.aP * 2 ^ P.sP)
      - (∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o) / 2 ^ P.sP) * (2 ^ x.aP * 2 ^ P.sP)
      = Kl P C x.label x.label * (2 ^ x.aP * 2 ^ P.sP) + (guardN P x.label : ℝ) * 2 ^ x.aP - x.rho
        - (∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o) * 2 ^ x.aP := by
    field_simp
  have hle : (Kl P C x.label x.label + (guardN P x.label : ℝ) / 2 ^ P.sP - x.rho / (2 ^ x.aP * 2 ^ P.sP)
      - (∑ o ∈ range 9, if o = x.label then 0 else piN P heads C x.label o) / 2 ^ P.sP) * (2 ^ x.aP * 2 ^ P.sP) ≤ 0 := by
    rw [key]
    linarith
  have hpos : (0 : ℝ) < 2 ^ x.aP * 2 ^ P.sP := mul_pos hA hSP
  by_contra hc
  rw [not_le] at hc
  have := mul_pos (sub_pos.2 hc) hpos
  linarith

end CAP.VR
