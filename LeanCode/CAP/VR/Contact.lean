module

public import CAP.VR.Exact

/-!
# Virtual-root certificates: the contacts of an exact certificate

Let the bound `Bn / Bd` of an exact certificate be attained at a configuration of its piece. Then every inequality
in the proof of the bound is an equality. In particular the minorant of every pair touches the function at the
inner product of the pair, and the sum-of-squares side of the minorant identity vanishes at the minorant point.
Each of its terms is nonnegative, so each of them vanishes. A term `a * ζ ^ 2` of the exact part of a weight `g`
with a number `a ≥ 1` gives `g * ζ ^ 2 = 0`.

* `dg_const`: the polynomial of the digits of a mask of the degree zero is a number;
* `sosGoX_zero_cons`, `term_zero`: the terms of a vanishing sum-of-squares side vanish;
* `pair_tight`: if the bound is attained, the inequality of every pair is an equality;
* `mino_sos_zero`: the sum-of-squares side of the minorant identity then vanishes;
* `contact_of`: the checker `contactOk` is sound: the contact `Contact` of the record type holds;
* `contacts`: **the theorem of contacts**, for nine points of the unit sphere of `ℝ⁴`.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open MvPolynomial Finset

/-! ## A mask of the degree zero -/

theorem mvar_zero {A : Type*} [CommSemiring A] (L : Lay) (x : A) (i : ℕ) (H : ℕ → ℕ → ℕ → A) (p c : ℕ) :
    mvar L x i H 0 p c = H 0 p c := by
  unfold mvar
  split_ifs
  · rfl
  · rfl

/-- The mask of the degree zero and of the class zero is the monomial `1`. -/
theorem HP_zero (L : Lay) (p : ℕ) : HP L 0 p 0 = 1 := by
  unfold HP mgen
  rw [mvar_zero, mvar_zero, mvar_zero, mvar_zero, mvar_zero]
  rfl

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ}

/-- **The polynomial of the digits of a mask of the degree zero** is the digit of the number at the slot zero. -/
theorem dg_const (y : Fin 5 → ℝ) (W : ℕ) (L : Lay) (dp wb d : ℕ) :
    (realOps W L y).dg 0 dp 0 wb d = (((d &&& mask (2 * W)) &&& mask wb : ℕ) : ℝ) := by
  show evR y (dgPoly W L 0 dp 0 wb d) = _
  unfold dgPoly
  rw [HP_zero]
  have hs : (1 : NPoly).support = {0} := MvPolynomial.support_one
  rw [hs, Finset.sum_singleton, MvPolynomial.coeff_zero_one, mul_one, pos_zero]
  have e : slot (2 * W) d 0 = d &&& mask (2 * W) := rfl
  rw [e, evR_monomial_double]
  simp

/-! ## Terms that vanish -/

theorem atomVal_zero_of : ∀ (ats : List Atom), sqAtoms (realOps W L y) ats = 0 →
    ∀ t ∈ ats, atomVal (realOps W L y) t = 0
  | [], _, t, ht => absurd ht List.not_mem_nil
  | a :: l, h, t, ht => by
    have h' : atomVal (realOps W L y) a + sqAtoms (realOps W L y) l = 0 := h
    have ha := atomVal_nonneg (W := W) (L := L) (y := y) a
    have hl := sqAtoms_nonneg (W := W) (L := L) (y := y) l
    rcases List.mem_cons.1 ht with rfl | ht'
    · linarith
    · exact atomVal_zero_of l (by linarith) t ht'

theorem anyAtom_spec {p : Atom → Bool} : ∀ {ats : List Atom}, anyAtom p ats = true → ∃ t ∈ ats, p t = true
  | [], h => absurd h Bool.false_ne_true
  | a :: l, h => by
    have h' : (p a || anyAtom p l) = true := h
    simp only [Bool.or_eq_true] at h'
    rcases h' with h1 | h2
    · exact ⟨a, List.mem_cons_self, h1⟩
    · obtain ⟨t, ht, hp⟩ := anyAtom_spec h2
      exact ⟨t, List.mem_cons_of_mem _ ht, hp⟩

theorem isOne_spec {c : ℕ} : ∀ {l : List ℕ}, isOne c l = true → l = [c]
  | [], h => absurd h Bool.false_ne_true
  | a :: t, h => by
    have h' : (Nat.beq a c && isNil t) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    cases t with
    | nil => rw [Nat.eq_of_beq_eq_true h1]
    | cons b t' => exact absurd h2 Bool.false_ne_true

theorem isTwo_spec {c0 c1 : ℕ} : ∀ {l : List ℕ}, isTwo c0 c1 l = true → l = [c0, c1]
  | [], h => absurd h Bool.false_ne_true
  | a :: t, h => by
    have h' : (Nat.beq a c0 && isOne c1 t) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨h1, h2⟩ := h'
    rw [Nat.eq_of_beq_eq_true h1, isOne_spec h2]

theorem lenW_one : ∀ {ws : List Weight}, Nat.ble 1 (lenW ws) = true → ∃ w l, ws = w :: l
  | [], h => absurd h Bool.false_ne_true
  | w :: l, _ => ⟨w, l, rfl⟩

theorem lenW_two : ∀ {ws : List Weight}, Nat.ble 2 (lenW ws) = true → ∃ w0 w1 l, ws = w0 :: w1 :: l
  | [], h => absurd h Bool.false_ne_true
  | [_], h => absurd h Bool.false_ne_true
  | w0 :: w1 :: l, _ => ⟨w0, w1, l, rfl⟩

/-- A term with a constant polynomial `A` is `a * ζ ^ 2` with a positive number `a`. -/
theorem atomConst_val {t : Atom} (h : atomConst W t = true) (y : Fin 5 → ℝ) (L : Lay) :
    ∃ a : ℝ, 0 < a ∧ atomVal (realOps W L y) t = a * dot5 (realOps W L y) t.wz t.zc t.zp t.zn ^ 2 := by
  have h' : (Nat.beq t.cls 0 && Nat.beq t.delta 0
      && Nat.ble 1 (Nat.land (Nat.land t.d (mask (Nat.mul 2 W))) (mask t.wb))) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨hc, hd⟩, hpos⟩ := h'
  refine ⟨(((t.d &&& mask (2 * W)) &&& mask t.wb : ℕ) : ℝ), ?_, ?_⟩
  · have h1 : 1 ≤ (t.d &&& mask (2 * W)) &&& mask t.wb := Nat.le_of_ble_eq_true hpos
    exact Nat.cast_pos.2 h1
  · show (realOps W L y).dg t.delta t.dp t.cls t.wb t.d
      * (dot5 (realOps W L y) t.wz t.zc t.zp t.zn * dot5 (realOps W L y) t.wz t.zc t.zp t.zn) = _
    rw [Nat.eq_of_beq_eq_true hc, Nat.eq_of_beq_eq_true hd, dg_const, sq]

/-- From `g * ∑ terms = 0`: `g * ζ ^ 2 = 0` for a term `a * ζ ^ 2` with a positive number `a`. -/
theorem term_zero {g : ℝ} {ats : List Atom} (hz : g * sqAtoms (realOps W L y) ats = 0) {t : Atom} (ht : t ∈ ats)
    (hc : atomConst W t = true) : g * dot5 (realOps W L y) t.wz t.zc t.zp t.zn ^ 2 = 0 := by
  rcases mul_eq_zero.1 hz with h1 | h1
  · rw [h1, zero_mul]
  · obtain ⟨a, ha, hv⟩ := atomConst_val hc y L
    have h2 := atomVal_zero_of ats h1 t ht
    rw [hv] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 ha.ne'
    · rw [h3, mul_zero]

/-! ## The polynomials `ζ` of the contacts -/

theorem dot5_one (w c zp zn : ℕ) :
    dot5 (realOps W L y) w [c] zp zn
      = ((zp &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c - ((zn &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c := by
  show ((0 : ℕ) : ℝ) + ((Nat.land zp (mask w) : ℕ) : ℝ) * (realOps W L y).mono c
    - (((0 : ℕ) : ℝ) + ((Nat.land zn (mask w) : ℕ) : ℝ) * (realOps W L y).mono c) = _
  simp only [Nat.cast_zero, zero_add]
  rfl

theorem dot5_two (w c0 c1 zp zn : ℕ) :
    dot5 (realOps W L y) w [c0, c1] zp zn
      = (((zp &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c0
          + (((zp >>> w) &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c1)
        - (((zn &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c0
          + (((zn >>> w) &&& mask w : ℕ) : ℝ) * (realOps W L y).mono c1) := by
  show ((0 : ℕ) : ℝ) + ((Nat.land zp (mask w) : ℕ) : ℝ) * (realOps W L y).mono c0
      + ((Nat.land (Nat.shiftRight zp w) (mask w) : ℕ) : ℝ) * (realOps W L y).mono c1
    - (((0 : ℕ) : ℝ) + ((Nat.land zn (mask w) : ℕ) : ℝ) * (realOps W L y).mono c0
      + ((Nat.land (Nat.shiftRight zn w) (mask w) : ℕ) : ℝ) * (realOps W L y).mono c1) = _
  simp only [Nat.cast_zero, zero_add]
  rfl

theorem mono_at (m0 m1 : ℝ) (c : ℕ) :
    (realOps W L ![m0, m1, 0, 0, 0]).mono c
      = m0 ^ dig c 0 * m1 ^ dig c 1 * (0 : ℝ) ^ dig c 2 * (0 : ℝ) ^ dig c 3 * (0 : ℝ) ^ dig c 4 := rfl

theorem mono_v0 (m0 m1 : ℝ) : (realOps W L ![m0, m1, 0, 0, 0]).mono 0 = 1 := by
  rw [mono_at, show dig 0 0 = 0 from rfl, show dig 0 1 = 0 from rfl, show dig 0 2 = 0 from rfl,
    show dig 0 3 = 0 from rfl, show dig 0 4 = 0 from rfl]
  simp

theorem mono_v1 (m0 m1 : ℝ) : (realOps W L ![m0, m1, 0, 0, 0]).mono 1 = m0 := by
  rw [mono_at, show dig 1 0 = 1 from rfl, show dig 1 1 = 0 from rfl, show dig 1 2 = 0 from rfl,
    show dig 1 3 = 0 from rfl, show dig 1 4 = 0 from rfl]
  simp

theorem mono_v2 (m0 m1 : ℝ) : (realOps W L ![m0, m1, 0, 0, 0]).mono 2 = m0 ^ 2 := by
  rw [mono_at, show dig 2 0 = 2 from rfl, show dig 2 1 = 0 from rfl, show dig 2 2 = 0 from rfl,
    show dig 2 3 = 0 from rfl, show dig 2 4 = 0 from rfl]
  simp

theorem mono_v16 (m0 m1 : ℝ) : (realOps W L ![m0, m1, 0, 0, 0]).mono 16 = m1 := by
  rw [mono_at, show dig 16 0 = 0 from rfl, show dig 16 1 = 1 from rfl, show dig 16 2 = 0 from rfl,
    show dig 16 3 = 0 from rfl, show dig 16 4 = 0 from rfl]
  simp

/-- The term `a * (X ^ c) ^ 2`. -/
theorem atomMono_spec {c : ℕ} {t : Atom} (h : atomMono W c t = true) :
    atomConst W t = true ∧ ∀ (y : Fin 5 → ℝ) (L : Lay),
      dot5 (realOps W L y) t.wz t.zc t.zp t.zn = (realOps W L y).mono c := by
  have h' : (atomConst W t && Nat.beq t.wz 1 && isOne c t.zc && Nat.beq t.zp 1 && Nat.beq t.zn 0) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h'
  refine ⟨h1, fun y L => ?_⟩
  rw [Nat.eq_of_beq_eq_true h2, isOne_spec h3, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, dot5_one,
    show (1 &&& mask 1 : ℕ) = 1 from rfl, show (0 &&& mask 1 : ℕ) = 0 from rfl]
  simp

/-- The term `a * (qa * X₀ ^ 2 - qb) ^ 2`. -/
theorem atomQuad_spec {qa qb : ℕ} {t : Atom} (h : atomQuad W qa qb t = true) :
    atomConst W t = true ∧ ∀ (y : Fin 5 → ℝ) (L : Lay), dot5 (realOps W L y) t.wz t.zc t.zp t.zn
      = (qa : ℝ) * (realOps W L y).mono 2 - (qb : ℝ) * (realOps W L y).mono 0 := by
  have h' : (atomConst W t && isTwo 0 2 t.zc && Nat.beq (Nat.land t.zp (mask t.wz)) 0
      && Nat.beq (Nat.land (Nat.shiftRight t.zp t.wz) (mask t.wz)) qa
      && Nat.beq (Nat.land t.zn (mask t.wz)) qb
      && Nat.beq (Nat.land (Nat.shiftRight t.zn t.wz) (mask t.wz)) 0) = true := h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
  refine ⟨h1, fun y L => ?_⟩
  have e3 : (t.zp &&& mask t.wz) = 0 := Nat.eq_of_beq_eq_true h3
  have e4 : ((t.zp >>> t.wz) &&& mask t.wz) = qa := Nat.eq_of_beq_eq_true h4
  have e5 : (t.zn &&& mask t.wz) = qb := Nat.eq_of_beq_eq_true h5
  have e6 : ((t.zn >>> t.wz) &&& mask t.wz) = 0 := Nat.eq_of_beq_eq_true h6
  rw [isTwo_spec h2, dot5_two, e3, e4, e5, e6]
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]

/-! ## A sum-of-squares side that vanishes -/

theorem sosGoX_acc_le : ∀ (ws : List Weight) (ex : List ExW) (locs : List ℝ) (acc : ℝ), (∀ g ∈ locs, 0 ≤ g) →
    acc ≤ sosGoX (realOps W L y) ws ex locs acc
  | [], _, _, _, _ => le_rfl
  | w :: l, ex, locs, acc, hl => by
    rw [sosGoX_cons]
    refine le_trans ?_ (sosGoX_acc_le l _ _ _ (fun g hg => hl g (tlA_mem hg)))
    show acc ≤ acc + hdA (realOps W L y) locs
      * (((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * sqBlocks (realOps W L y) w.blocks
        + ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats)
    have := mul_nonneg (hdA_nonneg (W := W) (L := L) (y := y) hl)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg (Nat.shiftLeft 1 w.a)) (sqBlocks_nonneg (W := W) (L := L) (y := y) w.blocks))
        (mul_nonneg (Nat.cast_nonneg (Nat.shiftLeft 1 (hdX ex).b)) (sqAtoms_nonneg (W := W) (L := L) (y := y) (hdX ex).ats)))
    linarith

/-- **If the sum-of-squares side vanishes**, then the first weight times the exact part of the first weight
vanishes, and the rest of the sum vanishes. -/
theorem sosGoX_zero_cons {w : Weight} {l : List Weight} {ex : List ExW} {locs : List ℝ} (hl : ∀ g ∈ locs, 0 ≤ g)
    (h : sosGoX (realOps W L y) (w :: l) ex locs 0 = 0) :
    hdA (realOps W L y) locs * sqAtoms (realOps W L y) (hdX ex).ats = 0
      ∧ sosGoX (realOps W L y) l (tlX ex) (tlA locs) 0 = 0 := by
  rw [sosGoX_cons] at h
  have hg := hdA_nonneg (W := W) (L := L) (y := y) hl
  have hB := sqBlocks_nonneg (W := W) (L := L) (y := y) w.blocks
  have hA := sqAtoms_nonneg (W := W) (L := L) (y := y) (hdX ex).ats
  have ha : (0 : ℝ) ≤ ((Nat.shiftLeft 1 w.a : ℕ) : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) < ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) := by
    rw [cast_shl1]
    positivity
  have h' : sosGoX (realOps W L y) l (tlX ex) (tlA locs)
      (0 + hdA (realOps W L y) locs
        * (((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * sqBlocks (realOps W L y) w.blocks
          + ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats)) = 0 := h
  have hle := sosGoX_acc_le (W := W) (L := L) (y := y) l (tlX ex) (tlA locs)
    (0 + hdA (realOps W L y) locs
      * (((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * sqBlocks (realOps W L y) w.blocks
        + ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats))
    (fun g hg => hl g (tlA_mem hg))
  rw [h'] at hle
  have h1 := mul_nonneg hg (mul_nonneg ha hB)
  have h2 := mul_nonneg hg (mul_nonneg hb.le hA)
  have h3 : hdA (realOps W L y) locs * (((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats)
      = 0 := by nlinarith
  have h4 : hdA (realOps W L y) locs
      * (((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * sqBlocks (realOps W L y) w.blocks
        + ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ) * sqAtoms (realOps W L y) (hdX ex).ats) = 0 := by nlinarith
  constructor
  · have h5 : ((Nat.shiftLeft 1 (hdX ex).b : ℕ) : ℝ)
        * (hdA (realOps W L y) locs * sqAtoms (realOps W L y) (hdX ex).ats) = 0 := by linarith
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 hb.ne'
    · exact h6
  · rw [h4, add_zero] at h'
    exact h'

/-! ## If the bound is attained, every pair is tight -/

theorem tight_of_sums {a f : ℕ → ℕ → ℝ} (hle : ∀ j ∈ range 9, ∀ i ∈ range j, a i j ≤ f i j)
    (hs : ∑ j ∈ range 9, ∑ i ∈ range j, f i j ≤ ∑ j ∈ range 9, ∑ i ∈ range j, a i j) {i j : ℕ} (hij : i < j)
    (hj : j < 9) : f i j ≤ a i j := by
  have hz : ∑ j ∈ range 9, ∑ i ∈ range j, (f i j - a i j) = 0 := by
    have hnn : 0 ≤ ∑ j ∈ range 9, ∑ i ∈ range j, (f i j - a i j) :=
      Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi => sub_nonneg.2 (hle j hj i hi)
    have e : ∑ j ∈ range 9, ∑ i ∈ range j, (f i j - a i j)
        = ∑ j ∈ range 9, ∑ i ∈ range j, f i j - ∑ j ∈ range 9, ∑ i ∈ range j, a i j := by
      simp only [Finset.sum_sub_distrib]
    linarith
  have hz1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j hj => Finset.sum_nonneg fun i hi => sub_nonneg.2 (hle j hj i hi))).1 hz j (Finset.mem_range.2 hj)
  have hz2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => sub_nonneg.2 (hle j (Finset.mem_range.2 hj) i hi))).1 hz1 i (Finset.mem_range.2 hij)
  linarith

section

variable {P : Par} {heads : List RecH} {C : Conf}

/-- **If the bound of an exact certificate is attained, the inequality of every pair is an equality.** -/
theorem pair_tight {den Bn Bd : ℕ} (hlab : labelsOk P heads = true) (hck : CheckedX P heads den)
    (hb : boundOkX P heads den Bn Bd = true) (hin : InPiece P heads C)
    (hE : ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) ≤ (Bn : ℝ) / Bd) {i j : ℕ} (hij : i < j) (hj : j < 9) :
    (den : ℝ) / (2 - 2 * C.t i j)
      ≤ (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP + 2 * Kl P C i j
        + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP := by
  obtain ⟨hden, hBd, hR⟩ := boundOkX_real hb
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  have hBdR : (0 : ℝ) < Bd := by exact_mod_cast hBd
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  have hsum := energy_sum P heads C
    (fun i j => (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP)
    (fun i j => (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP + 2 * Kl P C i j
      + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP)
    (fun l => (guardN P l : ℝ) / 2 ^ P.sP)
    (fun j _ i _ => le_rfl)
    (fun l hl => labelX hlab hck hin (Finset.mem_range.1 hl))
  have e2 : (∑ j ∈ range 9, ∑ i ∈ range j, (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP)
      + ∑ l ∈ range 9, (guardN P l : ℝ) / 2 ^ P.sP
      = (((∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cp : ℝ)) + ∑ l ∈ range 9, (guardN P l : ℝ))
        - ∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cn : ℝ)) / 2 ^ P.sP := by
    simp only [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [e2] at hsum
  have e1 : ∑ j ∈ range 9, ∑ i ∈ range j, (den : ℝ) / (2 - 2 * C.t i j)
      = den * ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h1 : (den : ℝ) * ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) ≤ den * (Bn / Bd) :=
    mul_le_mul_of_nonneg_left hE hdenR.le
  have h2 : (den : ℝ) * (Bn / Bd)
      ≤ (((∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cp : ℝ)) + ∑ l ∈ range 9, (guardN P l : ℝ))
        - ∑ j ∈ range 9, ∑ i ∈ range j, ((hdOf P heads i j).cn : ℝ)) / 2 ^ P.sP := by
    rw [le_div_iff₀ hSP]
    have e3 : (den : ℝ) * (Bn / Bd) * 2 ^ P.sP = (Bn : ℝ) * den * 2 ^ P.sP / Bd := by ring
    rw [e3, div_le_iff₀ hBdR]
    linarith
  refine tight_of_sums (a := fun i j => (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP
      + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP)
    (f := fun i j => (den : ℝ) / (2 - 2 * C.t i j))
    (fun j hj i hi => pairX hlab hck hin (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)) ?_ hij hj
  rw [e1]
  linarith

variable {i j : ℕ} {h : RecH} {y : Fin 5 → ℝ} {σu σv m0 m1 : ℝ}

/-- **The sum-of-squares side of the minorant identity vanishes** where the minorant touches the function. -/
theorem mino_sos_zero (F : RecFacts P heads C i j h y σu σv m0 m1) {mx : MinoX} {ex : List ExW} {den : ℕ}
    (hLm : LayoutInj mx.L) (hmx : minoOkX P h mx ex den = true) (hr : mx.rho = 0)
    (ht : (den : ℝ) / (2 - 2 * C.t i j) ≤ poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP) :
    sosGoX (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) mx.ws ex
      (minoLocs (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) P h (2 ^ minoMM h * C.t i j) (minoMM h)) 0 = 0 := by
  have hmin := minoOkX_sound hLm hmx (mcube_of F)
  have hmx' : (Nat.beq (Nat.add (Nat.add mx.aH (minoMM h)) P.sP) (Nat.succ mx.E) && exwOk mx.W mx.L ex
      && runOk mx.L mx.W mx.wr mx.rho mx.ws (minoValX (pairOps mx.W mx.L) P h mx ex den) (minoValX (absOps mx.L) P h mx ex den)
        (minoValX degOps P h mx ex den) (minoValX (pdegOps mx.L.pm) P h mx ex den) (minoValX (posOps mx.L) P h mx ex den)
        (minoValX (clsOps mx.L.pv) P h mx ex den)) = true := hmx
  simp only [Bool.and_eq_true] at hmx'
  have hsc : mx.aH + minoMM h + P.sP = mx.E + 1 := Nat.eq_of_beq_eq_true hmx'.1.1
  have hS := sosGoX_nonneg (W := mx.W) (L := mx.L) (y := ![m0, m1, 0, 0, 0]) mx.ws ex _ 0 (F.mlocs mx.W mx.L) le_rfl
  rw [minoValX_real F, hr] at hmin
  have hlow := (abs_le.1 hmin).1
  have hE1 : (2 : ℝ) ^ mx.aH * 2 ^ minoMM h * 2 ^ P.sP = 2 * 2 ^ mx.E := by
    rw [← pow_add, ← pow_add, hsc, pow_succ]
    ring
  have hSP : (0 : ℝ) < 2 ^ P.sP := by positivity
  have hEp : (0 : ℝ) < 2 ^ mx.E := by positivity
  have hidp : (1 : ℝ) ≤ h.hid := by exact_mod_cast F.hid1
  have hgp : (0 : ℝ) < (h.hid : ℝ) + h.hin - h.hip := by
    have : (h.hip : ℝ) < (h.hid : ℝ) + h.hin := by exact_mod_cast F.hi1
    linarith
  have hd0 : (0 : ℝ) < 1 - C.t i j := by
    have := F.ivhi
    nlinarith
  have e : (2 : ℝ) ^ mx.aH * ((2 ^ minoMM h - 2 ^ minoMM h * C.t i j) * poly2 P.wP h.hex h.hp h.hn m0 m1)
      = (2 ^ mx.aH * 2 ^ minoMM h * 2 ^ P.sP) * ((1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
    field_simp
  rw [e, hE1] at hlow
  have hq : (den : ℝ) ≤ 2 * ((1 - C.t i j) * (poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP)) := by
    have h2 : (0 : ℝ) < 2 - 2 * C.t i j := by linarith
    rw [div_le_iff₀ h2] at ht
    linarith
  have hprod := mul_nonneg hEp.le (sub_nonneg.2 hq)
  simp only [Nat.cast_zero, neg_zero] at hlow
  refine le_antisymm ?_ hS
  nlinarith

/-! ## The contacts -/

/-- `2 ^ mM` times the inner product of a pair of a record type whose minorant has one variable, as a function of
this variable. -/
noncomputable def minoTR (h : RecH) (m : ℝ) : ℝ :=
  if h.hform = 1 then (h.hc0p : ℝ) * 2 ^ h.hj + 2 ^ h.hm * m - (h.hc0n : ℝ) * 2 ^ h.hj
  else (h.c0p : ℝ) + 2 ^ h.jd * m - (h.c0n : ℝ)

theorem minoT_uni {h : RecH} (hb : minoBiv h = false) (W : ℕ) (L : Lay) (m0 m1 : ℝ) :
    minoT (realOps W L ![m0, m1, 0, 0, 0]) h = minoTR h m0 := by
  unfold minoT minoTR
  rw [hb]
  by_cases hf : h.hform = 1
  · have hb1 : Nat.beq h.hform 1 = true := by
      rw [hf]
      rfl
    rw [if_pos hf, hb1]
    show ((Nat.shiftLeft h.hc0p h.hj : ℕ) : ℝ)
      + ((Nat.shiftLeft 1 h.hm : ℕ) : ℝ) * var (realOps W L ![m0, m1, 0, 0, 0]) 0
      - ((Nat.shiftLeft h.hc0n h.hj : ℕ) : ℝ) = _
    rw [vec0, cast_shl1, cast_shl, cast_shl]
  · rw [if_neg hf, beq_false_of_ne hf]
    show ((h.c0p : ℕ) : ℝ) + ((Nat.shiftLeft 1 h.jd : ℕ) : ℝ) * var (realOps W L ![m0, m1, 0, 0, 0]) 0
      - ((h.c0n : ℕ) : ℝ) = _
    rw [vec0, cast_shl1]

/-- The weights of the minorant of a record type whose minorant has one variable. -/
theorem minoLocs_uni_eq {h : RecH} (hb : minoBiv h = false) (W : ℕ) (L : Lay) (y' : Fin 5 → ℝ) (t : ℝ) (mM : ℕ) :
    minoLocs (realOps W L y') P h (2 ^ mM * t) mM
      = [2 ^ mM * ((h.lod : ℝ) * t + h.lon - h.lop), 2 ^ mM * ((h.hip : ℝ) - h.hin - h.hid * t)] := by
  unfold minoLocs
  rw [hb]
  show [(h.lod : ℝ) * (2 ^ mM * t) + ((Nat.mul h.lon (Nat.shiftLeft 1 mM) : ℕ) : ℝ)
        - ((Nat.mul h.lop (Nat.shiftLeft 1 mM) : ℕ) : ℝ),
      ((Nat.mul h.hip (Nat.shiftLeft 1 mM) : ℕ) : ℝ)
        - ((h.hid : ℝ) * (2 ^ mM * t) + ((Nat.mul h.hin (Nat.shiftLeft 1 mM) : ℕ) : ℝ))] = _
  rw [cast_mul_shl, cast_mul_shl, cast_mul_shl, cast_mul_shl]
  have e1 : (h.lod : ℝ) * (2 ^ mM * t) + (h.lon : ℝ) * 2 ^ mM - (h.lop : ℝ) * 2 ^ mM
      = 2 ^ mM * ((h.lod : ℝ) * t + h.lon - h.lop) := by ring
  have e2 : (h.hip : ℝ) * 2 ^ mM - ((h.hid : ℝ) * (2 ^ mM * t) + (h.hin : ℝ) * 2 ^ mM)
      = 2 ^ mM * ((h.hip : ℝ) - h.hin - h.hid * t) := by ring
  rw [e1, e2]

/-- The first weight of the minorant of a record type whose minorant has two variables is `1`. -/
theorem minoLocs_biv_hd {h : RecH} (hb : minoBiv h = true) (W : ℕ) (L : Lay) (y' : Fin 5 → ℝ) (T : ℝ) (mM : ℕ) :
    hdA (realOps W L y') (minoLocs (realOps W L y') P h T mM) = 1 := by
  unfold minoLocs
  rw [hb]
  show ((1 : ℕ) : ℝ) = 1
  simp

theorem minoBiv_kind {h : RecH} (hb : minoBiv h = true) : h.kind = 3 ∨ h.kind = 4 := by
  have h' : (Nat.beq h.kind 3 || Nat.beq h.kind 4) = true := hb
  simp only [Bool.or_eq_true] at h'
  rcases h' with h1 | h1
  · exact Or.inl (Nat.eq_of_beq_eq_true h1)
  · exact Or.inr (Nat.eq_of_beq_eq_true h1)

theorem minoBiv_false {h : RecH} (h3 : h.kind ≠ 3) (h4 : h.kind ≠ 4) : minoBiv h = false := by
  unfold minoBiv
  rw [beq_false_of_ne h3, beq_false_of_ne h4]
  rfl

/-- The interval of a record type has an interior: its two weights do not vanish together. -/
theorem ivOk_real {h : RecH} (hv : ivOk h = true) (t : ℝ) :
    ¬ ((h.lod : ℝ) * t + h.lon - h.lop = 0 ∧ (h.hip : ℝ) - h.hin - h.hid * t = 0) := by
  have hlt : h.lop * h.hid + h.hin * h.lod < h.hip * h.lod + h.lon * h.hid := lt_of_blt hv
  have hltR : (h.lop : ℝ) * h.hid + h.hin * h.lod < h.hip * h.lod + h.lon * h.hid := by exact_mod_cast hlt
  rintro ⟨e1, e2⟩
  have k1 : (h.lod : ℝ) * t * h.hid = ((h.lop : ℝ) - h.lon) * h.hid := by
    rw [show (h.lod : ℝ) * t = (h.lop : ℝ) - h.lon by linarith]
  have k2 : (h.hid : ℝ) * t * h.lod = ((h.hip : ℝ) - h.hin) * h.lod := by
    rw [show (h.hid : ℝ) * t = (h.hip : ℝ) - h.hin by linarith]
  have k3 : (h.lod : ℝ) * t * h.hid = (h.hid : ℝ) * t * h.lod := by ring
  nlinarith

/-- **The contact of a pair** of a record type, for the inner product `t` of the pair:

* AA, BB: `t` is the lower end of the interval of the record type;
* A r, B r: `t = 0`;
* AB: the variable of the minorant vanishes;
* a ring type: the variable `m` of the minorant satisfies `qa * m ^ 2 = qb`. -/
def Contact (h : RecH) (qa qb : ℕ) (t : ℝ) : Prop :=
  (h.kind ≤ 1 → (h.lod : ℝ) * t + h.lon = h.lop)
    ∧ (minoBiv h = true → t = 0)
    ∧ (h.kind = 2 → minoTR h 0 = 2 ^ minoMM h * t)
    ∧ (5 ≤ h.kind → ∃ m : ℝ, minoTR h m = 2 ^ minoMM h * t ∧ (qa : ℝ) * m ^ 2 = qb)

/-- **The checker of the contacts is sound.** If the minorant of a pair touches the function, and the exact parts of
the minorant have the terms that `contactOk` asks for, then the contact of the record type holds. -/
theorem contact_of (F : RecFacts P heads C i j h y σu σv m0 m1) {mx : MinoX} {ex : List ExW} {den qa qb : ℕ}
    (hLm : LayoutInj mx.L) (hmx : minoOkX P h mx ex den = true) (hr : mx.rho = 0)
    (hct : contactOk h mx ex qa qb = true)
    (ht : (den : ℝ) / (2 - 2 * C.t i j) ≤ poly2 P.wP h.hex h.hp h.hn m0 m1 / 2 ^ P.sP) :
    Contact h qa qb (C.t i j) := by
  have h0 := mino_sos_zero F hLm hmx hr ht
  have hl := F.mlocs mx.W mx.L
  have hT := F.mT mx.W mx.L
  have h2M : (2 : ℝ) ^ minoMM h ≠ 0 := by positivity
  unfold contactOk at hct
  refine ⟨fun hk => ?_, fun hbv => ?_, fun hk => ?_, fun hk => ?_⟩
  · -- the lower end
    rw [Nat.ble_eq_true_of_le hk] at hct
    have hct' : (Nat.ble 1 (lenW mx.ws) && anyAtom (atomMono mx.W 0) (hdX ex).ats) = true := hct
    simp only [Bool.and_eq_true] at hct'
    obtain ⟨hlen, hat⟩ := hct'
    have hbiv : minoBiv h = false := minoBiv_false (by omega) (by omega)
    rw [minoLocs_uni_eq hbiv] at h0 hl
    obtain ⟨w, l, hws⟩ := lenW_one hlen
    rw [hws] at h0
    obtain ⟨hz, -⟩ := sosGoX_zero_cons hl h0
    obtain ⟨t, htm, htp⟩ := anyAtom_spec hat
    obtain ⟨hc, hζ⟩ := atomMono_spec htp
    have hg : 2 ^ minoMM h * ((h.lod : ℝ) * C.t i j + h.lon - h.lop)
        * dot5 (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) t.wz t.zc t.zp t.zn ^ 2 = 0 := term_zero hz htm hc
    rw [hζ, mono_v0, one_pow, mul_one] at hg
    rcases mul_eq_zero.1 hg with h1 | h1
    · exact absurd h1 h2M
    · linarith
  · -- both variables of the minorant vanish
    obtain hk | hk := minoBiv_kind hbv
    all_goals
      rw [ble_false (by omega), hbv] at hct
      have hct' : (Nat.ble 1 (lenW mx.ws) && anyAtom (atomMono mx.W 16) (hdX ex).ats
        && anyAtom (atomMono mx.W 2) (hdX ex).ats) = true := hct
      simp only [Bool.and_eq_true] at hct'
      obtain ⟨⟨hlen, hat1⟩, hat2⟩ := hct'
      obtain ⟨w, l, hws⟩ := lenW_one hlen
      rw [hws] at h0
      obtain ⟨hz, -⟩ := sosGoX_zero_cons hl h0
      rw [minoLocs_biv_hd hbv] at hz
      obtain ⟨t1, htm1, htp1⟩ := anyAtom_spec hat1
      obtain ⟨hc1, hζ1⟩ := atomMono_spec htp1
      have hg1 := term_zero hz htm1 hc1
      rw [hζ1, mono_v16, one_mul] at hg1
      obtain ⟨t2, htm2, htp2⟩ := anyAtom_spec hat2
      obtain ⟨hc2, hζ2⟩ := atomMono_spec htp2
      have hg2 := term_zero hz htm2 hc2
      rw [hζ2, mono_v2, one_mul] at hg2
      have hm1 : m1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hg1
      have hm0 : m0 = 0 := by
        have := pow_eq_zero_iff (two_ne_zero) |>.1 hg2
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      unfold minoT at hT
      rw [hbv] at hT
      have hT' : ((Nat.shiftLeft 1 h.mS : ℕ) : ℝ) * var (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) 0
          + var (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) 1 = 2 ^ minoMM h * C.t i j := hT
      rw [vec0, vec1, hm0, hm1, mul_zero, add_zero] at hT'
      rcases mul_eq_zero.1 hT'.symm with h1 | h1
      · exact absurd h1 h2M
      · exact h1
  · -- the variable of the minorant vanishes
    have hbiv : minoBiv h = false := minoBiv_false (by omega) (by omega)
    rw [ble_false (by omega), hbiv, show Nat.beq h.kind 2 = true from by rw [hk]; rfl] at hct
    have hct' : (Nat.ble 2 (lenW mx.ws) && ivOk h && anyAtom (atomMono mx.W 1) (hdX ex).ats
      && anyAtom (atomMono mx.W 1) (hdX (tlX ex)).ats) = true := hct
    simp only [Bool.and_eq_true] at hct'
    obtain ⟨⟨⟨hlen, hiv⟩, hat0⟩, hat1⟩ := hct'
    rw [minoLocs_uni_eq hbiv] at h0 hl
    obtain ⟨w0, w1, l, hws⟩ := lenW_two hlen
    rw [hws] at h0
    obtain ⟨hz0, h0'⟩ := sosGoX_zero_cons hl h0
    obtain ⟨hz1, -⟩ := sosGoX_zero_cons (fun g hg => hl g (tlA_mem hg)) h0'
    obtain ⟨t0, htm0, htp0⟩ := anyAtom_spec hat0
    obtain ⟨hc0, hζ0⟩ := atomMono_spec htp0
    have hg0 : 2 ^ minoMM h * ((h.lod : ℝ) * C.t i j + h.lon - h.lop)
        * dot5 (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) t0.wz t0.zc t0.zp t0.zn ^ 2 = 0 := term_zero hz0 htm0 hc0
    obtain ⟨t1, htm1, htp1⟩ := anyAtom_spec hat1
    obtain ⟨hc1, hζ1⟩ := atomMono_spec htp1
    have hg1 : 2 ^ minoMM h * ((h.hip : ℝ) - h.hin - h.hid * C.t i j)
        * dot5 (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) t1.wz t1.zc t1.zp t1.zn ^ 2 = 0 := term_zero hz1 htm1 hc1
    rw [hζ0, mono_v1] at hg0
    rw [hζ1, mono_v1] at hg1
    have hm0 : m0 = 0 := by
      by_contra hne
      have hsq : m0 ^ 2 ≠ 0 := pow_ne_zero 2 hne
      have a0 := (mul_eq_zero.1 hg0).resolve_right hsq
      have a1 := (mul_eq_zero.1 hg1).resolve_right hsq
      exact ivOk_real hiv (C.t i j) ⟨(mul_eq_zero.1 a0).resolve_left h2M, (mul_eq_zero.1 a1).resolve_left h2M⟩
    rw [minoT_uni hbiv, hm0] at hT
    exact hT
  · -- the variable of the minorant is a root of `qa * m ^ 2 - qb`
    have hbiv : minoBiv h = false := minoBiv_false (by omega) (by omega)
    rw [ble_false (by omega), hbiv, beq_false_of_ne (by omega)] at hct
    have hct' : (Nat.ble 2 (lenW mx.ws) && ivOk h && anyAtom (atomQuad mx.W qa qb) (hdX ex).ats
      && anyAtom (atomQuad mx.W qa qb) (hdX (tlX ex)).ats) = true := hct
    simp only [Bool.and_eq_true] at hct'
    obtain ⟨⟨⟨hlen, hiv⟩, hat0⟩, hat1⟩ := hct'
    rw [minoLocs_uni_eq hbiv] at h0 hl
    obtain ⟨w0, w1, l, hws⟩ := lenW_two hlen
    rw [hws] at h0
    obtain ⟨hz0, h0'⟩ := sosGoX_zero_cons hl h0
    obtain ⟨hz1, -⟩ := sosGoX_zero_cons (fun g hg => hl g (tlA_mem hg)) h0'
    obtain ⟨t0, htm0, htp0⟩ := anyAtom_spec hat0
    obtain ⟨hc0, hζ0⟩ := atomQuad_spec htp0
    have hg0 : 2 ^ minoMM h * ((h.lod : ℝ) * C.t i j + h.lon - h.lop)
        * dot5 (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) t0.wz t0.zc t0.zp t0.zn ^ 2 = 0 := term_zero hz0 htm0 hc0
    obtain ⟨t1, htm1, htp1⟩ := anyAtom_spec hat1
    obtain ⟨hc1, hζ1⟩ := atomQuad_spec htp1
    have hg1 : 2 ^ minoMM h * ((h.hip : ℝ) - h.hin - h.hid * C.t i j)
        * dot5 (realOps mx.W mx.L ![m0, m1, 0, 0, 0]) t1.wz t1.zc t1.zp t1.zn ^ 2 = 0 := term_zero hz1 htm1 hc1
    rw [hζ0, mono_v2, mono_v0, mul_one] at hg0
    rw [hζ1, mono_v2, mono_v0, mul_one] at hg1
    have hq : (qa : ℝ) * m0 ^ 2 - qb = 0 := by
      by_contra hne
      have hsq : ((qa : ℝ) * m0 ^ 2 - qb) ^ 2 ≠ 0 := pow_ne_zero 2 hne
      have a0 := (mul_eq_zero.1 hg0).resolve_right hsq
      have a1 := (mul_eq_zero.1 hg1).resolve_right hsq
      exact ivOk_real hiv (C.t i j) ⟨(mul_eq_zero.1 a0).resolve_left h2M, (mul_eq_zero.1 a1).resolve_left h2M⟩
    refine ⟨m0, ?_, by linarith⟩
    rw [← minoT_uni hbiv mx.W mx.L m0 m1]
    exact hT

/-- **The minorants of an exact certificate with the terms of the contacts**: every record type has a checked minorant
identity with the residual zero whose exact parts contain the terms that give its contact. -/
structure ContactsX (P : Par) (heads : List RecH) (den qa qb : ℕ) : Prop where
  minos : ∀ k, k < lenH heads → ∃ (x : MinoX) (ex : List ExW), LayoutInj x.L
    ∧ minoOkX P (nthH heads k) x ex den = true ∧ x.rho = 0 ∧ contactOk (nthH heads k) x ex qa qb = true

/-- **The theorem of contacts, in coordinates.** If the energy of a configuration of the piece of a checked exact
certificate is at most the bound of the certificate, then every pair has the contact of its record type. -/
theorem contacts_coords {den Bn Bd qa qb : ℕ} (hlab : labelsOk P heads = true) (hck : CheckedX P heads den)
    (hct : ContactsX P heads den qa qb) (hb : boundOkX P heads den Bn Bd = true) (hin : InPiece P heads C)
    (hE : ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) ≤ (Bn : ℝ) / Bd) {i j : ℕ} (hij : i < j) (hj : j < 9) :
    Contact (hdOf P heads i j) qa qb (C.t i j) := by
  obtain ⟨y, σu, σv, m0, m1, Fa⟩ := rec_facts hlab hin hij hj
  obtain ⟨x, ex, hxL, hxok, hxr⟩ := hck.recs _ (pair_index_lt hlab hij hj)
  obtain ⟨mx, mex, hmL, hmok, hmr, hmc⟩ := hct.minos _ (pair_index_lt hlab hij hj)
  have h1 := rec_partX Fa hxL hxok
  rw [hxr] at h1
  simp only [Nat.cast_zero, zero_div, sub_zero] at h1
  have h2 := pair_tight hlab hck hb hin hE hij hj
  exact contact_of Fa hmL hmok hmr hmc (le_trans h2 h1)

end

/-! ## Points of the sphere -/

section

variable {P : Par} {heads : List RecH}

/-- **The theorem of contacts.** Let the labels, the identities and the bound `Bn / Bd` of an exact virtual-root
certificate be checked, and let the minorants have the terms of the contacts. If the energy of a configuration of
the piece of the certificate is at most `Bn / Bd`, then the inner product of every pair of points has the contact of
the record type of the pair. -/
theorem contacts {den Bn Bd qa qb : ℕ} (hlab : labelsOk P heads = true) (hck : CheckedX P heads den)
    (hct : ContactsX P heads den qa qb) (hb : boundOkX P heads den Bn Bd = true)
    {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)} (hin : InPieceS P heads x e f)
    (hE : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 ≤ (Bn : ℝ) / Bd) (i j : Fin 9) (hij : i < j) :
    Contact (hdOf P heads i j) qa qb (inner ℝ (x i) (x j)) := by
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
  have hE' : ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * (confOf x e f (b 2) (b 3)).t i j) ≤ (Bn : ℝ) / Bd := by
    rw [← sum_fin_pairs 9 (fun i j => 1 / (2 - 2 * (confOf x e f (b 2) (b 3)).t i j))]
    refine le_of_eq_of_le ?_ hE
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hT, pt_coe, pt_coe, norm_sub_sq_real, hin.unit, hin.unit]
    congr 1
    ring
  have hc := contacts_coords hlab hck hct hb hI hE' (i := i) (j := j) hij j.isLt
  rw [hT, pt_coe, pt_coe] at hc
  exact hc

/-! ## The minorants with the terms of the contacts, from lists -/

/-- The minorant identities with exact parts of a list of record types, with the terms of the contacts. -/
def MinosCtX (P : Par) (den qa qb : ℕ) : List RecH → List MinoX → List (List ExW) → Prop
  | [], _, _ => True
  | h :: hs, x :: xs, e :: es =>
    (LayoutInj x.L ∧ minoOkX P h x e den = true ∧ x.rho = 0 ∧ contactOk h x e qa qb = true) ∧ MinosCtX P den qa qb hs xs es
  | _ :: _, _, _ => False

theorem minosCtX_nth {den qa qb : ℕ} : ∀ (hs : List RecH) (xs : List MinoX) (es : List (List ExW)),
    MinosCtX P den qa qb hs xs es → ∀ k, k < lenH hs → ∃ (x : MinoX) (ex : List ExW), LayoutInj x.L
      ∧ minoOkX P (nthH hs k) x ex den = true ∧ x.rho = 0 ∧ contactOk (nthH hs k) x ex qa qb = true
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | _ :: _, _ :: _, [], hf, _, _ => False.elim hf
  | _ :: _, x :: _, e :: _, hr, 0, _ => ⟨x, e, hr.1⟩
  | _ :: hs, _ :: xs, _ :: es, hr, k + 1, hk => minosCtX_nth hs xs es hr.2 k (Nat.lt_of_succ_lt_succ hk)

/-- **The minorants with the terms of the contacts**, from the lists of the minorants and of their exact parts. -/
theorem contactsX_of {den qa qb : ℕ} {ms : List MinoX} {mes : List (List ExW)}
    (h : MinosCtX P den qa qb heads ms mes) : ContactsX P heads den qa qb where
  minos := minosCtX_nth heads ms mes h

end

end CAP.VR
