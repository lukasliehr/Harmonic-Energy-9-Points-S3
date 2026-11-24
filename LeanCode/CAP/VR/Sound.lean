module

public import CAP.VR.Columns
public import CAP.VR.Rel

/-!
# Virtual-root certificates: soundness of the checkers of the identities

The six evaluations of the checker are related to the polynomial of an identity (`opsRel_pair`,
`opsRel_abs`, `opsRel_deg`, `opsRel_pdeg`, `opsRel_pos`, `opsRel_cls`), and the polynomial is related to its
values at real points (`opsRel_real`). Hence, if a checker accepts and the layout is injective on the
admissible monomials, the residual of the identity is bounded by `rho` on the cube `[-1, 1] ^ 5`:
`recordOk_sound`, `minoOk_sound`, `clsOk_sound`, and `recordOkX_sound`, `minoOkX_sound` for the identities with
exact parts. The residual is stated with the operations on real numbers (`realOps`), whose values
`CAP/VR/Real.lean` describes.
-/

@[expose] public section

namespace CAP.VR

open MvPolynomial Finset

variable {W : ℕ} {L : Lay}

/-! ## The pairs -/

theorem opsRel_pair (hL : LayoutInj L) : OpsRel (RPair W L) (BlkGood W L) (pairOps W L) (polyOps W L) where
  add := fun {a a' b b'} h1 h2 => by
    show ((a.1 + a'.1 : ℕ) : ℤ) - ((a.2 + a'.2 : ℕ) : ℤ) = ev W L (b + b')
    unfold RPair at h1 h2
    rw [map_add, ← h1, ← h2]
    push_cast
    ring
  sub := fun {a a' b b'} h1 h2 => by
    show ((a.1 + a'.2 : ℕ) : ℤ) - ((a.2 + a'.1 : ℕ) : ℤ) = ev W L (b - b')
    unfold RPair at h1 h2
    rw [map_sub, ← h1, ← h2]
    push_cast
    ring
  mul := fun {a a' b b'} h1 h2 => by
    show ((a.1 * a'.1 + a.2 * a'.2 : ℕ) : ℤ) - ((a.1 * a'.2 + a.2 * a'.1 : ℕ) : ℤ) = ev W L (b * b')
    unfold RPair at h1 h2
    rw [map_mul, ← h1, ← h2]
    push_cast
    ring
  smul := fun n {a b} h1 => by
    show ((n * a.1 : ℕ) : ℤ) - ((n * a.2 : ℕ) : ℤ) = ev W L (C (n : ℤ) * b)
    unfold RPair at h1
    rw [map_mul, ← h1, show ev W L (C (n : ℤ)) = (n : ℤ) from eval_C _]
    push_cast
    ring
  nat := fun n => by
    show ((n : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = ev W L (C (n : ℤ))
    rw [show ev W L (C (n : ℤ)) = (n : ℤ) from eval_C _]
    simp
  mono := fun c => by
    show ((1 <<< (W * posOf L c) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = ev W L (monomial (expo c) 1)
    rw [ev_monomial, pos_expo, Nat.one_shiftLeft]
    simp
  sq := fun δ dp cls wb col r hg => by
    show ((CAP.Wsos.sqSum (mask wb * maskAt W L δ dp cls) (maskAt W L δ dp cls <<< (wb - 1)) col r : ℕ) : ℤ) - ((0 : ℕ) : ℤ)
      = ev W L (∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2)
    rw [sqSum_cast, map_sum, Nat.cast_zero, sub_zero]
    refine sum_congr rfl fun i _ => ?_
    rw [map_pow, ← masked_value hL hg]
  dg := fun δ dp cls wb d hg => by
    show ((d &&& (mask wb * maskAt (2 * W) L δ dp cls) : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = ev W L (dgPoly W L δ dp cls wb d)
    rw [Nat.cast_zero, sub_zero]
    exact dg_value hL hg d

/-! ## The bounds for the coefficients -/

theorem RAbs.sum_range {f : ℕ → Poly} {n : ℕ} : ∀ r : ℕ, (∀ i, i < r → RAbs n (f i)) → RAbs (r * n) (∑ i ∈ range r, f i)
  | 0, _ => ⟨0, by simpa using Maj.zero, by simp⟩
  | r + 1, h => by
    obtain ⟨G1, h1, h2⟩ := RAbs.sum_range r fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨G2, h3, h4⟩ := h r (Nat.lt_succ_self r)
    refine ⟨G1 + G2, ?_, ?_⟩
    · rw [sum_range_succ]
      exact h1.add h3
    · rw [map_add, Nat.succ_mul]
      exact add_le_add h2 h4

theorem opsRel_abs : OpsRel RAbs (BlkGood W L) (absOps L) (polyOps W L) where
  add := fun {a a' b b'} h1 h2 => by
    obtain ⟨G1, m1, c1⟩ := h1
    obtain ⟨G2, m2, c2⟩ := h2
    exact ⟨G1 + G2, m1.add m2, by rw [map_add]; exact add_le_add c1 c2⟩
  sub := fun {a a' b b'} h1 h2 => by
    obtain ⟨G1, m1, c1⟩ := h1
    obtain ⟨G2, m2, c2⟩ := h2
    exact ⟨G1 + G2, m1.sub m2, by rw [map_add]; exact add_le_add c1 c2⟩
  mul := fun {a a' b b'} h1 h2 => by
    obtain ⟨G1, m1, c1⟩ := h1
    obtain ⟨G2, m2, c2⟩ := h2
    exact ⟨G1 * G2, m1.mul m2, by rw [map_mul]; exact Nat.mul_le_mul c1 c2⟩
  smul := fun n {a b} h1 => by
    obtain ⟨G1, m1, c1⟩ := h1
    refine ⟨C n * G1, (Maj.C (by simp)).mul m1, ?_⟩
    rw [map_mul, show csum (C n) = n from eval_C _]
    exact Nat.mul_le_mul_left _ c1
  nat := fun n => ⟨C n, Maj.C (by simp), by rw [show csum (C n) = n from eval_C _]; exact le_refl n⟩
  mono := fun c => ⟨monomial (expo c) 1, Maj.monomial _ (by simp), by rw [csum_monomial]; exact le_refl 1⟩
  sq := fun δ dp cls wb col r hg => by
    show RAbs (r * (maskAt 0 L δ dp cls <<< (wb - 1) * (maskAt 0 L δ dp cls <<< (wb - 1))))
      (∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2)
    refine RAbs.sum_range r fun i _ => ?_
    obtain ⟨G1, m1, c1⟩ := masked_abs (W := W) (L := L) (δ := δ) (dp := dp) (cls := cls) hg.wb1 (col i)
    exact ⟨G1 * G1, by rw [pow_two]; exact m1.mul m1, by rw [map_mul]; exact Nat.mul_le_mul c1 c1⟩
  dg := fun δ dp cls wb d _ => dg_abs d

/-! ## The bounds for the degree, the pair degree and the slots -/

theorem masked_RW {w : (Fin 5 →₀ ℕ) → ℕ} {n δ dp cls wb : ℕ} (x : ℕ)
    (h : ∀ e ∈ (HP L δ dp cls).support, w e ≤ n) : RW w n (maskedPoly W L δ dp cls wb x) :=
  fun e he => h e (masked_support he)

theorem sq_RW {w : (Fin 5 →₀ ℕ) → ℕ} (hw : AddW w) {n δ dp cls wb : ℕ} (col : ℕ → ℕ) (r : ℕ)
    (h : ∀ e ∈ (HP L δ dp cls).support, w e ≤ n) :
    RW w (n + n) (∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2) :=
  RW.sum _ _ fun i _ => by
    rw [pow_two]
    exact RW.mul hw (masked_RW (col i) h) (masked_RW (col i) h)

/-- A set of operations on bounds for an additive weight. -/
theorem opsRel_w {w : (Fin 5 →₀ ℕ) → ℕ} (hw : AddW w) {O : Ops ℕ} (hadd : O.add = maxN) (hsub : O.sub = maxN)
    (hmul : O.mul = Nat.add) (hsmul : ∀ n x, O.smul n x = x) (hnat : ∀ n, O.nat n = 0) (hmono : ∀ c, O.mono c = w (expo c))
    (hsq : ∀ δ dp cls wb col r, RW w (O.sq δ dp cls wb col r) ((polyOps W L).sq δ dp cls wb col r))
    (hdg : ∀ δ dp cls wb d, RW w (O.dg δ dp cls wb d) ((polyOps W L).dg δ dp cls wb d)) :
    OpsRel (RW w) (BlkGood W L) O (polyOps W L) where
  add := fun h1 h2 => by rw [hadd]; exact h1.add h2
  sub := fun h1 h2 => by rw [hsub]; exact h1.sub h2
  mul := fun h1 h2 => by rw [hmul]; exact RW.mul hw h1 h2
  smul := fun n {a b} h1 => by rw [hsmul]; exact h1.smul n
  nat := fun n => by rw [hnat]; exact RW.nat hw n 0
  mono := fun c => by rw [hmono]; exact RW.monomial _ _
  sq := fun δ dp cls wb col r _ => hsq δ dp cls wb col r
  dg := fun δ dp cls wb d _ => hdg δ dp cls wb d

/-- A bound for an additive weight of the monomials of the polynomial of the digits. -/
theorem dg_RW {w : (Fin 5 →₀ ℕ) → ℕ} (hw : AddW w) {n δ dp cls wb : ℕ} (d : ℕ)
    (h : ∀ e ∈ (HP L δ dp cls).support, w e ≤ n) : RW w (n + n) (dgPoly W L δ dp cls wb d) := fun e he => by
  obtain ⟨e₀, he₀, rfl⟩ := dg_support he
  rw [hw.add]
  exact add_le_add (h e₀ he₀) (h e₀ he₀)

theorem opsRel_deg : OpsRel (RW edeg) (BlkGood W L) degOps (polyOps W L) :=
  opsRel_w addW_edeg rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun c => (edeg_expo c).symm)
    (fun δ dp cls wb col r => by
      show RW edeg (2 * δ) _
      rw [two_mul]
      exact sq_RW addW_edeg col r fun e he => (HP_spec L δ dp cls e he).1)
    fun δ dp cls wb d => by
      show RW edeg (2 * δ) _
      rw [two_mul]
      exact dg_RW addW_edeg d fun e he => (HP_spec L δ dp cls e he).1

theorem opsRel_pdeg : OpsRel (RW (epdeg L.pm)) (BlkGood W L) (pdegOps L.pm) (polyOps W L) :=
  opsRel_w (addW_epdeg L.pm) rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun c => (epdeg_expo L.pm c).symm)
    (fun δ dp cls wb col r => by
      show RW (epdeg L.pm) (2 * dp) _
      rw [two_mul]
      exact sq_RW (addW_epdeg L.pm) col r fun e he => (HP_spec L δ dp cls e he).2.1)
    fun δ dp cls wb d => by
      show RW (epdeg L.pm) (2 * dp) _
      rw [two_mul]
      exact dg_RW (addW_epdeg L.pm) d fun e he => (HP_spec L δ dp cls e he).2.1

theorem k_le_kmax (L : Lay) (i : Fin 5) : L.k i ≤ kmax L := by
  unfold kmax
  simp only [maxN_eq]
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  · exact (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)

theorem pos_le (L : Lay) (e : Fin 5 →₀ ℕ) : pos L e ≤ kmax L * edeg e := by
  unfold pos edeg
  rw [mul_sum]
  exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ (k_le_kmax L i)

theorem opsRel_pos : OpsRel (RW (pos L)) (BlkGood W L) (posOps L) (polyOps W L) :=
  opsRel_w (addW_pos L) rfl rfl rfl (fun _ _ => rfl) (fun _ => rfl) (fun c => (pos_expo L c).symm)
    (fun δ dp cls wb col r => by
      show RW (pos L) (2 * δ * kmax L) _
      have : 2 * δ * kmax L = kmax L * δ + kmax L * δ := by ring
      rw [this]
      exact sq_RW (addW_pos L) col r fun e he =>
        (pos_le L e).trans (Nat.mul_le_mul_left _ (HP_spec L δ dp cls e he).1)) fun δ dp cls wb d => by
      show RW (pos L) (2 * δ * kmax L) _
      have : 2 * δ * kmax L = kmax L * δ + kmax L * δ := by ring
      rw [this]
      exact dg_RW (addW_pos L) d fun e he =>
        (pos_le L e).trans (Nat.mul_le_mul_left _ (HP_spec L δ dp cls e he).1)

/-! ## The parity classes -/

theorem opsRel_cls : OpsRel (RCls L.pv) (BlkGood W L) (clsOps L.pv) (polyOps W L) where
  add := fun h1 h2 => h1.add h2
  sub := fun h1 h2 => h1.sub h2
  mul := fun h1 h2 => h1.mul h2
  smul := fun n {a b} h1 => h1.smul n
  nat := fun n => RCls.nat n
  mono := fun c => by
    show RCls L.pv (1 <<< clsOf L.pv c) (monomial (expo c) 1)
    rw [← ecls_expo]
    exact RCls.monomial _ _
  sq := fun δ dp cls wb col r _ => by
    show RCls L.pv 1 (∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2)
    refine RCls.sum _ _ fun i _ e he => ?_
    rw [pow_two] at he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_mul he
    rw [ecls_add, (HP_spec L δ dp cls a (masked_support ha)).2.2, (HP_spec L δ dp cls b (masked_support hb)).2.2,
      Nat.xor_self]
    rfl
  dg := fun δ dp cls wb d _ => by
    show RCls L.pv 1 (dgPoly W L δ dp cls wb d)
    intro e he
    obtain ⟨e₀, _, rfl⟩ := dg_support he
    rw [ecls_add, Nat.xor_self]
    rfl

/-! ## The values at real points -/

/-- The operations of the checker on real numbers, at the point `y`. -/
noncomputable def realOps (W : ℕ) (L : Lay) (y : Fin 5 → ℝ) : Ops ℝ where
  add := fun a b => a + b
  sub := fun a b => a - b
  mul := fun a b => a * b
  smul := fun n a => (n : ℝ) * a
  nat := fun n => (n : ℝ)
  mono := fun c => y 0 ^ dig c 0 * y 1 ^ dig c 1 * y 2 ^ dig c 2 * y 3 ^ dig c 3 * y 4 ^ dig c 4
  sq := fun δ dp cls wb col r => evR y ((polyOps W L).sq δ dp cls wb col r)
  dg := fun δ dp cls wb d => evR y ((polyOps W L).dg δ dp cls wb d)

theorem evR_C (y : Fin 5 → ℝ) (n : ℕ) : evR y (C (n : ℤ)) = (n : ℝ) := by
  show eval₂ (Int.castRingHom ℝ) y (C (n : ℤ)) = _
  rw [eval₂_C]
  simp

theorem opsRel_real (y : Fin 5 → ℝ) :
    OpsRel (fun (F : Poly) (r : ℝ) => evR y F = r) (BlkGood W L) (polyOps W L) (realOps W L y) where
  add := fun {a a' b b'} h1 h2 => by
    show evR y (a + a') = b + b'
    rw [map_add, h1, h2]
  sub := fun {a a' b b'} h1 h2 => by
    show evR y (a - a') = b - b'
    rw [map_sub, h1, h2]
  mul := fun {a a' b b'} h1 h2 => by
    show evR y (a * a') = b * b'
    rw [map_mul, h1, h2]
  smul := fun n {a b} h1 => by
    show evR y (C (n : ℤ) * a) = (n : ℝ) * b
    rw [map_mul, evR_C, h1]
  nat := fun n => evR_C y n
  mono := fun c => by
    show eval₂ (Int.castRingHom ℝ) y (monomial (expo c) 1) = _
    rw [eval₂_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_five]
    simp only [expo_apply, map_one, one_mul]
    rfl
  sq := fun _ _ _ _ _ _ _ => rfl
  dg := fun _ _ _ _ _ _ => rfl

/-- The value of a monomial with even exponents is a square. -/
theorem evR_monomial_double (y : Fin 5 → ℝ) (e : Fin 5 →₀ ℕ) (n : ℕ) :
    evR y (monomial (e + e) (n : ℤ)) = n * (∏ i, y i ^ e i) ^ 2 := by
  show eval₂ (Int.castRingHom ℝ) y (monomial (e + e) (n : ℤ)) = _
  rw [eval₂_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), pow_two, ← Finset.prod_mul_distrib]
  simp only [Finsupp.coe_add, Pi.add_apply, pow_add, eq_intCast, Int.cast_natCast]

/-- The polynomial of the digits is nonnegative at every real point. -/
theorem realOps_dg_nonneg (y : Fin 5 → ℝ) (δ dp cls wb d : ℕ) : 0 ≤ (realOps W L y).dg δ dp cls wb d := by
  show 0 ≤ evR y (dgPoly W L δ dp cls wb d)
  unfold dgPoly
  rw [map_sum]
  exact sum_nonneg fun e _ => by
    rw [evR_monomial_double]
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- The squares of a block are nonnegative. -/
theorem realOps_sq_nonneg (y : Fin 5 → ℝ) (δ dp cls wb : ℕ) (col : ℕ → ℕ) (r : ℕ) :
    0 ≤ (realOps W L y).sq δ dp cls wb col r := by
  show 0 ≤ evR y (∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2)
  rw [map_sum]
  exact sum_nonneg fun i _ => by rw [map_pow]; exact sq_nonneg _

/-! ## The tests -/

theorem blocksOk_good : ∀ (bs : List WBlk), blocksOk W L bs = true → BlocksG (BlkGood W L) bs
  | [], _ => trivial
  | b :: bs, h => by
    have h' : (Nat.ble 1 b.wb && Nat.ble b.wb W && Nat.ble (Nat.mul 2 b.delta) L.D && Nat.ble (Nat.mul 2 b.dp) L.Dp
        && Nat.ble b.cls 3 && Nat.ble (Nat.shiftLeft (maskAt 0 L b.delta b.dp b.cls) b.wb) (Nat.shiftLeft 1 W)
        && blocksOk W L bs) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨⟨h1, _⟩, h3⟩, h4⟩, _⟩, h6⟩, h7⟩ := h'
    refine ⟨⟨Nat.le_of_ble_eq_true h1, ?_, Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4⟩, blocksOk_good bs h7⟩
    have := Nat.le_of_ble_eq_true h6
    have e1 : Nat.shiftLeft (maskAt 0 L b.delta b.dp b.cls) b.wb = maskAt 0 L b.delta b.dp b.cls * 2 ^ b.wb :=
      Nat.shiftLeft_eq _ _
    have e2 : Nat.shiftLeft 1 W = 2 ^ W := Nat.one_shiftLeft W
    rwa [e1, e2] at this

theorem weightsOk_good : ∀ (ws : List Weight), weightsOk W L ws = true → WeightsG (BlkGood W L) ws
  | [], _ => trivial
  | w :: ws, h => by
    have h' : (blocksOk W L w.blocks && weightsOk W L ws) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨blocksOk_good _ h'.1, weightsOk_good ws h'.2⟩

theorem atomsOk_good : ∀ (ats : List Atom), atomsOk W L ats = true → AtomsG (BlkGood W L) ats
  | [], _ => trivial
  | t :: ats, h => by
    have h' : (Nat.ble 1 t.wb && Nat.ble t.wb W && Nat.ble (Nat.mul 2 t.delta) L.D && Nat.ble (Nat.mul 2 t.dp) L.Dp
        && Nat.ble t.cls 3 && Nat.ble (Nat.shiftLeft (maskAt 0 L t.delta t.dp t.cls) t.wb) (Nat.shiftLeft 1 W)
        && atomsOk W L ats) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨⟨h1, _⟩, h3⟩, h4⟩, _⟩, h6⟩, h7⟩ := h'
    refine ⟨⟨Nat.le_of_ble_eq_true h1, ?_, Nat.le_of_ble_eq_true h3, Nat.le_of_ble_eq_true h4⟩, atomsOk_good ats h7⟩
    have := Nat.le_of_ble_eq_true h6
    have e1 : Nat.shiftLeft (maskAt 0 L t.delta t.dp t.cls) t.wb = maskAt 0 L t.delta t.dp t.cls * 2 ^ t.wb :=
      Nat.shiftLeft_eq _ _
    have e2 : Nat.shiftLeft 1 W = 2 ^ W := Nat.one_shiftLeft W
    rwa [e1, e2] at this

theorem exwOk_good : ∀ (ex : List ExW), exwOk W L ex = true → ExG (BlkGood W L) ex
  | [], _ => trivial
  | w :: ex, h => by
    have h' : (atomsOk W L w.ats && exwOk W L ex) = true := h
    rw [Bool.and_eq_true] at h'
    exact ⟨atomsOk_good _ h'.1, exwOk_good ex h'.2⟩

theorem cls_zero_of {cs c : ℕ} (h : cs &&& 14 = 0) (hc : c < 4) (ht : cs.testBit c = true) : c = 0 := by
  by_contra h0
  have h1 : (cs &&& 14).testBit c = true := by
    rw [Nat.testBit_and, ht]
    have : c = 1 ∨ c = 2 ∨ c = 3 := by omega
    rcases this with rfl | rfl | rfl <;> rfl
  rw [h] at h1
  simp at h1

/-- **The tests that all identities share.** If they accept the six values of a polynomial `F`, then the
absolute values of the coefficients of `F` have a sum of at most `rho`, and the blocks of the weights are
good. -/
theorem run_sound (hL : LayoutInj L) {wr rho : ℕ} {ws : List Weight} {val : ℕ × ℕ} {bound deg pdeg posb cs : ℕ} {F : Poly}
    (hrun : runOk L W wr rho ws val bound deg pdeg posb cs = true) (h1 : RPair W L val F) (h2 : RAbs bound F)
    (h3 : RW edeg deg F) (h4 : RW (epdeg L.pm) pdeg F) (h5 : RW (pos L) posb F) (h6 : RCls L.pv cs F) :
    ∑ e ∈ F.support, |coeff e F| ≤ (rho : ℤ) := by
  simp only [runOk, Bool.and_eq_true] at hrun
  obtain ⟨⟨⟨⟨⟨_, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hrun
  have hadm : ∀ e ∈ F.support, Adm L e := fun e he =>
    ⟨(h3 e he).trans (Nat.le_of_ble_eq_true a2), (h4 e he).trans (Nat.le_of_ble_eq_true a3),
      cls_zero_of (Nat.eq_of_beq_eq_true a4) (ecls_lt _ _) (h6 e he)⟩
  have hBW : bound + 2 ^ wr ≤ 2 ^ W := by
    have := Nat.le_of_ble_eq_true a5
    have e1 : Nat.shiftLeft 1 wr = 2 ^ wr := Nat.one_shiftLeft wr
    have e2 : Nat.shiftLeft 1 W = 2 ^ W := Nat.one_shiftLeft W
    rw [e1, e2] at this
    exact this
  exact residual_bound hL hadm h2 (fun e he => Nat.lt_succ_of_le (h5 e he)) h1 hBW a6

theorem run_weights {wr rho : ℕ} {ws : List Weight} {val : ℕ × ℕ} {bound deg pdeg posb cs : ℕ}
    (hrun : runOk L W wr rho ws val bound deg pdeg posb cs = true) : WeightsG (BlkGood W L) ws := by
  simp only [runOk, Bool.and_eq_true] at hrun
  exact weightsOk_good ws hrun.1.1.1.1.1

/-! ## The three checkers -/

theorem abs_real_le {F : Poly} {rho : ℕ} (h : ∑ e ∈ F.support, |coeff e F| ≤ (rho : ℤ)) {y : Fin 5 → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : |evR y F| ≤ (rho : ℝ) :=
  (abs_evR_le hy F).trans (by exact_mod_cast h)

/-- **Soundness of the checker of a record type**: the residual of the identity is bounded by `rho` on the cube. -/
theorem recordOk_sound {P : Par} {hd : RecH} {x : RecX} (hL : LayoutInj x.L) (h : recordOk P hd x = true)
    {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) : |recVal (realOps x.W x.L y) P hd x| ≤ (x.rho : ℝ) := by
  have h' : (recScalesOk P hd x
      && runOk x.L x.W x.wr x.rho x.ws (recVal (pairOps x.W x.L) P hd x) (recVal (absOps x.L) P hd x) (recVal degOps P hd x)
        (recVal (pdegOps x.L.pm) P hd x) (recVal (posOps x.L) P hd x) (recVal (clsOps x.L.pv) P hd x)) = true := h
  rw [Bool.and_eq_true] at h'
  have hg := run_weights h'.2
  have hb := run_sound hL h'.2 (recVal_rel (opsRel_pair hL) P hd x hg) (recVal_rel opsRel_abs P hd x hg)
    (recVal_rel opsRel_deg P hd x hg) (recVal_rel opsRel_pdeg P hd x hg) (recVal_rel opsRel_pos P hd x hg)
    (recVal_rel opsRel_cls P hd x hg)
  rw [← recVal_rel (opsRel_real y) P hd x hg]
  exact abs_real_le hb hy

theorem recordOk_scales {P : Par} {hd : RecH} {x : RecX} (h : recordOk P hd x = true) : recScalesOk P hd x = true := by
  have h' : (recScalesOk P hd x
      && runOk x.L x.W x.wr x.rho x.ws (recVal (pairOps x.W x.L) P hd x) (recVal (absOps x.L) P hd x) (recVal degOps P hd x)
        (recVal (pdegOps x.L.pm) P hd x) (recVal (posOps x.L) P hd x) (recVal (clsOps x.L.pv) P hd x)) = true := h
  rw [Bool.and_eq_true] at h'
  exact h'.1

/-- **Soundness of the checker of a minorant.** -/
theorem minoOk_sound {P : Par} {hd : RecH} {x : MinoX} (hL : LayoutInj x.L) (h : minoOk P hd x = true)
    {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) : |minoVal (realOps x.W x.L y) P hd x| ≤ (x.rho : ℝ) := by
  have h' : (Nat.beq (Nat.add (Nat.add x.aH (minoMM hd)) P.sP) (Nat.succ x.E)
      && runOk x.L x.W x.wr x.rho x.ws (minoVal (pairOps x.W x.L) P hd x) (minoVal (absOps x.L) P hd x) (minoVal degOps P hd x)
        (minoVal (pdegOps x.L.pm) P hd x) (minoVal (posOps x.L) P hd x) (minoVal (clsOps x.L.pv) P hd x)) = true := h
  rw [Bool.and_eq_true] at h'
  have hg := run_weights h'.2
  have hb := run_sound hL h'.2 (minoVal_rel (opsRel_pair hL) P hd x hg) (minoVal_rel opsRel_abs P hd x hg)
    (minoVal_rel opsRel_deg P hd x hg) (minoVal_rel opsRel_pdeg P hd x hg) (minoVal_rel opsRel_pos P hd x hg)
    (minoVal_rel opsRel_cls P hd x hg)
  rw [← minoVal_rel (opsRel_real y) P hd x hg]
  exact abs_real_le hb hy

/-- **Soundness of the checker of the identity of a label.** -/
theorem clsOk_sound {P : Par} {heads : List RecH} {x : ClsX} (hL : LayoutInj x.L) (h : clsOk P heads x = true)
    {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) : |clsVal (realOps x.W x.L y) P heads x| ≤ (x.rho : ℝ) := by
  have h' : (Nat.beq (Nat.add x.aP P.sP) x.E && Nat.beq (Nat.add x.aL P.sP) x.E && Nat.blt x.label 9
      && cScalesGo (CAP.Wsos.nth P.dcls x.label) (clsM P (CAP.Wsos.nth P.dcls x.label)) x.E P.kblocks x.aK P.sK 0
      && runOk x.L x.W x.wr x.rho [] (clsVal (pairOps x.W x.L) P heads x) (clsVal (absOps x.L) P heads x)
        (clsVal degOps P heads x) (clsVal (pdegOps x.L.pm) P heads x) (clsVal (posOps x.L) P heads x)
        (clsVal (clsOps x.L.pv) P heads x)) = true := h
  rw [Bool.and_eq_true] at h'
  have hb := run_sound hL h'.2 (clsVal_rel (opsRel_pair hL) P heads x) (clsVal_rel opsRel_abs P heads x)
    (clsVal_rel opsRel_deg P heads x) (clsVal_rel opsRel_pdeg P heads x) (clsVal_rel opsRel_pos P heads x)
    (clsVal_rel opsRel_cls P heads x)
  rw [← clsVal_rel (opsRel_real (W := x.W) (L := x.L) y) P heads x]
  exact abs_real_le hb hy

/-! ## The checkers of the identities with exact parts -/

/-- **Soundness of the checker of a record type with exact parts.** -/
theorem recordOkX_sound {P : Par} {hd : RecH} {x : RecX} {ex : List ExW} (hL : LayoutInj x.L)
    (h : recordOkX P hd x ex = true) {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    |recValX (realOps x.W x.L y) P hd x ex| ≤ (x.rho : ℝ) := by
  have h' : (recScalesOk P hd x && exwOk x.W x.L ex
      && runOk x.L x.W x.wr x.rho x.ws (recValX (pairOps x.W x.L) P hd x ex) (recValX (absOps x.L) P hd x ex)
        (recValX degOps P hd x ex) (recValX (pdegOps x.L.pm) P hd x ex) (recValX (posOps x.L) P hd x ex)
        (recValX (clsOps x.L.pv) P hd x ex)) = true := h
  simp only [Bool.and_eq_true] at h'
  have hg := run_weights h'.2
  have he := exwOk_good ex h'.1.2
  have hb := run_sound hL h'.2 (recValX_rel (opsRel_pair hL) P hd x ex hg he) (recValX_rel opsRel_abs P hd x ex hg he)
    (recValX_rel opsRel_deg P hd x ex hg he) (recValX_rel opsRel_pdeg P hd x ex hg he)
    (recValX_rel opsRel_pos P hd x ex hg he) (recValX_rel opsRel_cls P hd x ex hg he)
  rw [← recValX_rel (opsRel_real y) P hd x ex hg he]
  exact abs_real_le hb hy

theorem recordOkX_scales {P : Par} {hd : RecH} {x : RecX} {ex : List ExW} (h : recordOkX P hd x ex = true) :
    recScalesOk P hd x = true := by
  have h' : (recScalesOk P hd x && exwOk x.W x.L ex
      && runOk x.L x.W x.wr x.rho x.ws (recValX (pairOps x.W x.L) P hd x ex) (recValX (absOps x.L) P hd x ex)
        (recValX degOps P hd x ex) (recValX (pdegOps x.L.pm) P hd x ex) (recValX (posOps x.L) P hd x ex)
        (recValX (clsOps x.L.pv) P hd x ex)) = true := h
  simp only [Bool.and_eq_true] at h'
  exact h'.1.1

/-- **Soundness of the checker of a minorant with exact parts.** -/
theorem minoOkX_sound {P : Par} {hd : RecH} {x : MinoX} {ex : List ExW} {den : ℕ} (hL : LayoutInj x.L)
    (h : minoOkX P hd x ex den = true) {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) :
    |minoValX (realOps x.W x.L y) P hd x ex den| ≤ (x.rho : ℝ) := by
  have h' : (Nat.beq (Nat.add (Nat.add x.aH (minoMM hd)) P.sP) (Nat.succ x.E) && exwOk x.W x.L ex
      && runOk x.L x.W x.wr x.rho x.ws (minoValX (pairOps x.W x.L) P hd x ex den) (minoValX (absOps x.L) P hd x ex den)
        (minoValX degOps P hd x ex den) (minoValX (pdegOps x.L.pm) P hd x ex den) (minoValX (posOps x.L) P hd x ex den)
        (minoValX (clsOps x.L.pv) P hd x ex den)) = true := h
  simp only [Bool.and_eq_true] at h'
  have hg := run_weights h'.2
  have he := exwOk_good ex h'.1.2
  have hb := run_sound hL h'.2 (minoValX_rel (opsRel_pair hL) P hd x ex den hg he)
    (minoValX_rel opsRel_abs P hd x ex den hg he) (minoValX_rel opsRel_deg P hd x ex den hg he)
    (minoValX_rel opsRel_pdeg P hd x ex den hg he) (minoValX_rel opsRel_pos P hd x ex den hg he)
    (minoValX_rel opsRel_cls P hd x ex den hg he)
  rw [← minoValX_rel (opsRel_real y) P hd x ex den hg he]
  exact abs_real_le hb hy

end CAP.VR
