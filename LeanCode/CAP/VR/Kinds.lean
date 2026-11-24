module

public import CAP.VR.Cov

/-!
# Virtual-root certificates: the data of a pair of labels, for the six kinds of record types

`dpt P heads C i j` is the data of the pair `i < j` of labels: the class coordinates of the two labels with the
signs `fP`, `fQ`, and the last coordinate `lastV` (zero for the kinds AA and BB, the scaled deviation of the
inner product for the kinds AB, A r and B r, the centred inner product for a ring type). The theorems
`facts_k0`, …, `facts_k5` prove the facts `RecFacts` of the pair at its data, one for each kind; `rec_facts`
collects them.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ} {P : Par} {heads : List RecH} {C : Conf} {i j : ℕ}

/-! ## The data of a pair -/

/-- The last coordinate of the data of the pair `i < j`. -/
noncomputable def lastV (P : Par) (heads : List RecH) (C : Conf) (i j : ℕ) : ℝ :=
  if j < 2 then 0
  else if i < 2 then 2 ^ (hdOf P heads i j).mS * dev C i j
  else if j < 4 then 0
  else if i < 4 then 2 ^ (hdOf P heads i j).mS * dev C i j
  else (2 ^ (hdOf P heads i j).mTr * C.t i j - (((hdOf P heads i j).c0p : ℝ) - (hdOf P heads i j).c0n))
    / 2 ^ (hdOf P heads i j).jd

/-- **The data of the pair** `i < j` of labels. -/
noncomputable def dpt (P : Par) (heads : List RecH) (C : Conf) (i j : ℕ) : Fin 5 → ℝ :=
  ![fP i j * cp P C i, fQ i j * cq P C i, fP j i * cp P C j, fQ j i * cq P C j, lastV P heads C i j]

theorem dpt_cube (lab : LabOk P heads) (hin : InPiece P heads C) (hi : i < 9) (hj : j < 9)
    (hlast : |lastV P heads C i j| ≤ 1) : ∀ k, |dpt P heads C i j k| ≤ 1 := by
  intro k
  fin_cases k
  · show |(-1) ^ flipP i j * cp P C i| ≤ 1
    rw [abs_flip_mul]
    exact (cp_abs lab hin hi).1
  · show |(-1) ^ flipQ i j * cq P C i| ≤ 1
    rw [abs_flip_mul]
    exact (cp_abs lab hin hi).2
  · show |(-1) ^ flipP j i * cp P C j| ≤ 1
    rw [abs_flip_mul]
    exact (cp_abs lab hin hj).1
  · show |(-1) ^ flipQ j i * cq P C j| ≤ 1
    rw [abs_flip_mul]
    exact (cp_abs lab hin hj).2
  · exact hlast

/-! ## The signs -/

theorem sgA0 : sgA 0 = 1 := by
  unfold sgA
  norm_num

theorem sgA1 : sgA 1 = -1 := by
  unfold sgA
  norm_num

theorem fP_lt4 (hi : i < 4) : fP i j = 1 := by
  unfold fP
  rw [flipP_lt4 hi, pow_zero]

theorem fP_ring (hi : 4 ≤ i) : fP i j = if j = 1 then -1 else 1 := by
  unfold fP
  rw [flipP_ring hi]
  split_ifs <;> simp

theorem fQ_A (hi : i ≤ 1) : fQ i j = if j = 3 then -1 else 1 := by
  unfold fQ
  rw [flipQ_A hi]
  split_ifs <;> simp

theorem fQ_B (hi2 : 2 ≤ i) (hi : i ≤ 3) : fQ i j = if j = 1 then -1 else 1 := by
  unfold fQ
  rw [flipQ_B hi2 hi]
  split_ifs <;> simp

theorem fQ_R (hi : 4 ≤ i) : fQ i j = if j = 3 then -1 else 1 := by
  unfold fQ
  rw [flipQ_R hi]
  split_ifs <;> simp

theorem chiF0 (blk : Blk) (tp tq : ℕ) : chiF blk 0 tp tq = (-1) ^ (tq * blk.b) := by
  unfold chiF
  rw [if_pos rfl]

theorem chiF1 (blk : Blk) (tp tq : ℕ) : chiF blk 1 tp tq = (-1) ^ (tq * blk.a) := by
  unfold chiF
  rw [if_neg (by norm_num), if_pos rfl]

theorem chiF_ring {c : ℕ} (hc : 2 ≤ c) (blk : Blk) (tp tq : ℕ) : chiF blk c tp tq = (-1) ^ (tp * blk.a + tq * blk.b) := by
  unfold chiF
  rw [if_neg (by omega), if_neg (by omega)]

theorem clsM_ring {c : ℕ} (hc : 2 ≤ c) : clsM P c = 0 := by
  unfold clsM
  rw [beq_false_of_ne (by omega : c ≠ 0), beq_false_of_ne (by omega : c ≠ 1)]
  rfl

/-! ## The record types by kind -/

/-- The content of the check `headOk`. -/
theorem headOk_real {h : RecH} (hh : headOk h = true) :
    formOk h = true
      ∧ (h.kind = 0 → h.c1 = 0 ∧ h.s1 = 0 ∧ h.c2 = 0 ∧ h.s2 = 1)
      ∧ (h.kind = 1 → h.c1 = 1 ∧ h.s1 = 0 ∧ h.c2 = 1 ∧ h.s2 = 1)
      ∧ (h.kind = 2 → h.c1 = 0 ∧ h.s1 = 0 ∧ h.c2 = 1 ∧ h.s2 = 0)
      ∧ (h.kind = 3 → h.c1 = 0 ∧ h.s1 = 0 ∧ 2 ≤ h.c2)
      ∧ (h.kind = 4 → h.c1 = 1 ∧ h.s1 = 0 ∧ 2 ≤ h.c2)
      ∧ (h.kind = 5 → 2 ≤ h.c1 ∧ 2 ≤ h.c2 ∧ h.s1 ≤ 2 ∧ h.s2 ≤ 2) := by
  unfold headOk at hh
  rw [Bool.and_eq_true] at hh
  obtain ⟨hf, h2⟩ := hh
  refine ⟨hf, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · rw [hk] at h2
    have h2' : (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.beq h.c2 0 && Nat.beq h.s2 1) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.eq_of_beq_eq_true h2'.1.1.1, Nat.eq_of_beq_eq_true h2'.1.1.2, Nat.eq_of_beq_eq_true h2'.1.2,
      Nat.eq_of_beq_eq_true h2'.2⟩
  · rw [hk] at h2
    have h2' : (Nat.beq h.c1 1 && Nat.beq h.s1 0 && Nat.beq h.c2 1 && Nat.beq h.s2 1) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.eq_of_beq_eq_true h2'.1.1.1, Nat.eq_of_beq_eq_true h2'.1.1.2, Nat.eq_of_beq_eq_true h2'.1.2,
      Nat.eq_of_beq_eq_true h2'.2⟩
  · rw [hk] at h2
    have h2' : (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.beq h.c2 1 && Nat.beq h.s2 0) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.eq_of_beq_eq_true h2'.1.1.1, Nat.eq_of_beq_eq_true h2'.1.1.2, Nat.eq_of_beq_eq_true h2'.1.2,
      Nat.eq_of_beq_eq_true h2'.2⟩
  · rw [hk] at h2
    have h2' : (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.ble 2 h.c2) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.eq_of_beq_eq_true h2'.1.1, Nat.eq_of_beq_eq_true h2'.1.2, Nat.le_of_ble_eq_true h2'.2⟩
  · rw [hk] at h2
    have h2' : (Nat.beq h.c1 1 && Nat.beq h.s1 0 && Nat.ble 2 h.c2) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.eq_of_beq_eq_true h2'.1.1, Nat.eq_of_beq_eq_true h2'.1.2, Nat.le_of_ble_eq_true h2'.2⟩
  · rw [hk] at h2
    have h2' : (Nat.beq 5 5 && Nat.ble 2 h.c1 && Nat.ble 2 h.c2 && Nat.ble h.s1 2 && Nat.ble h.s2 2) = true := h2
    simp only [Bool.and_eq_true] at h2'
    exact ⟨Nat.le_of_ble_eq_true h2'.1.1.1.2, Nat.le_of_ble_eq_true h2'.1.1.2, Nat.le_of_ble_eq_true h2'.1.2,
      Nat.le_of_ble_eq_true h2'.2⟩

theorem recMT_k0 {h : RecH} (hk : h.kind = 0) : recMT P h = 2 * clsM P h.c1 := by
  unfold recMT
  rw [hk]
  rfl

theorem recMT_k1 {h : RecH} (hk : h.kind = 1) : recMT P h = 2 * clsM P h.c1 + 1 := by
  unfold recMT
  rw [hk]
  rfl

theorem recMT_k2 {h : RecH} (hk : h.kind = 2) : recMT P h = h.mS + clsM P h.c1 + clsM P h.c2 := by
  unfold recMT
  rw [hk]
  rfl

theorem recMT_k3 {h : RecH} (hk : h.kind = 3) : recMT P h = h.mS := by
  unfold recMT
  rw [hk]
  rfl

theorem recMT_k4 {h : RecH} (hk : h.kind = 4) : recMT P h = h.mS := by
  unfold recMT
  rw [hk]
  rfl

theorem recMT_k5 {h : RecH} (hk : h.kind = 5) : recMT P h = h.mTr := by
  unfold recMT
  rw [hk]
  rfl

theorem recT_k0 {h : RecH} (hk : h.kind = 0) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2 = 2 ^ (2 * clsM P h.c1) - 2 * (U1 * U1) := by
  unfold recT
  rw [hk]
  show ((Nat.shiftLeft 1 (Nat.mul 2 (clsM P h.c1)) : ℕ) : ℝ) - ((2 : ℕ) : ℝ) * (U1 * U1) = _
  rw [cast_shl1]
  show (2 : ℝ) ^ (2 * clsM P h.c1) - ((2 : ℕ) : ℝ) * (U1 * U1) = _
  norm_num

theorem recT_k1 {h : RecH} (hk : h.kind = 1) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2
      = 2 * 2 ^ (2 * clsM P h.c1) - ((U1 - U2) * (U1 - U2) + (V1 - V2) * (V1 - V2)) := by
  unfold recT
  rw [hk]
  show ((Nat.shiftLeft 2 (Nat.mul 2 (clsM P h.c1)) : ℕ) : ℝ) - ((U1 - U2) * (U1 - U2) + (V1 - V2) * (V1 - V2)) = _
  rw [cast_shl]
  show ((2 : ℕ) : ℝ) * 2 ^ (2 * clsM P h.c1) - _ = _
  norm_num

theorem recT_k2 {h : RecH} (hk : h.kind = 2) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2
      = 2 ^ (clsM P h.c1 + clsM P h.c2) * var (realOps W L y) 4
        + (2 ^ (h.mS + clsM P h.c2) * V1 + 2 ^ (h.mS + clsM P h.c1) * U2) := by
  unfold recT
  rw [hk]
  show ((Nat.shiftLeft 1 (Nat.add (clsM P h.c1) (clsM P h.c2)) : ℕ) : ℝ) * var (realOps W L y) 4
    + (((Nat.shiftLeft 1 (Nat.add h.mS (clsM P h.c2)) : ℕ) : ℝ) * V1
      + ((Nat.shiftLeft 1 (Nat.add h.mS (clsM P h.c1)) : ℕ) : ℝ) * U2) = _
  rw [cast_shl1, cast_shl1, cast_shl1]
  rfl

theorem recT_k3 {h : RecH} (hk : h.kind = 3) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2 = var (realOps W L y) 4 + 2 ^ h.mS * U2 := by
  unfold recT
  rw [hk]
  show var (realOps W L y) 4 + ((Nat.shiftLeft 1 h.mS : ℕ) : ℝ) * U2 = _
  rw [cast_shl1]

theorem recT_k4 {h : RecH} (hk : h.kind = 4) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2 = var (realOps W L y) 4 + 2 ^ h.mS * V2 := by
  unfold recT
  rw [hk]
  show var (realOps W L y) 4 + ((Nat.shiftLeft 1 h.mS : ℕ) : ℝ) * V2 = _
  rw [cast_shl1]

theorem recT_k5 {h : RecH} (hk : h.kind = 5) (U1 V1 U2 V2 : ℝ) :
    recT (realOps W L y) P h U1 V1 U2 V2 = (h.c0p : ℝ) + 2 ^ h.jd * var (realOps W L y) 4 - h.c0n := by
  unfold recT
  rw [hk]
  show ((h.c0p : ℕ) : ℝ) + ((Nat.shiftLeft 1 h.jd : ℕ) : ℝ) * var (realOps W L y) 4 - ((h.c0n : ℕ) : ℝ) = _
  rw [cast_shl1]

theorem i2_k0 {h : RecH} (hk : h.kind = 0) : i2p h = 0 ∧ i2q h = 1 := by
  constructor
  · show cond (Nat.beq h.kind 0) 0 2 = 0
    rw [hk]
    rfl
  · show cond (Nat.beq h.kind 0) 1 3 = 1
    rw [hk]
    rfl

theorem i2_ne0 {h : RecH} (hk : h.kind ≠ 0) : i2p h = 2 ∧ i2q h = 3 := by
  constructor
  · show cond (Nat.beq h.kind 0) 0 2 = 2
    rw [beq_false_of_ne hk]
    rfl
  · show cond (Nat.beq h.kind 0) 1 3 = 3
    rw [beq_false_of_ne hk]
    rfl

/-! ## The exchange polynomials -/

theorem pi1_fact (hij : i < j) (hc : ∀ c ∈ (hdOf P heads i j).p1ex, c < 256) (W : ℕ) (L : Lay) :
    dotS (realOps W L (dpt P heads C i j)) P.wP 0 0 0 1 (hdOf P heads i j).p1ex (hdOf P heads i j).p1p
      (hdOf P heads i j).p1n = piN P heads C i j := by
  rw [dotS_real0 (at01 _) P.wP _ hc]
  unfold piN
  rw [if_pos hij, headOf_lt hij]
  rfl

theorem pi2_fact (hij : i < j) (hk : (hdOf P heads i j).kind ≠ 0) (hc : ∀ c ∈ (hdOf P heads i j).p2ex, c < 256)
    (W : ℕ) (L : Lay) :
    dotS (realOps W L (dpt P heads C i j)) P.wP 0 0 (i2p (hdOf P heads i j)) (i2q (hdOf P heads i j))
      (hdOf P heads i j).p2ex (hdOf P heads i j).p2p (hdOf P heads i j).p2n = piN P heads C j i := by
  rw [(i2_ne0 hk).1, (i2_ne0 hk).2, dotS_real0 (at23 _) P.wP _ hc]
  unfold piN
  rw [if_neg (by omega), headOf_gt hij]
  rfl

/-! ## The minorants of the kinds A r, B r and of a ring type -/

theorem recHm_form0 {h : RecH} (hf0 : h.hform = 0) (hcodes : ∀ c ∈ h.hex, c < 256) {a b : ℝ}
    (hat : At y h.hia h.hib a b) (T : ℝ) (mT : ℕ) (W : ℕ) (L : Lay) :
    recHm (realOps W L y) P h T mT = poly2 P.wP h.hex h.hp h.hn a b := by
  unfold recHm
  rw [hf0]
  show dotS (realOps W L y) P.wP 0 0 h.hia h.hib h.hex h.hp h.hn = _
  exact dotS_real0 hat P.wP h.hex hcodes h.hp h.hn

/-- **The minorant of a record type A r or B r**, a polynomial in a coordinate of the ring point and in the
deviation. -/
theorem mino_biv {h : RecH} (hk : h.kind = 3 ∨ h.kind = 4) (hf0 : h.hform = 0) (hcodes : ∀ c ∈ h.hex, c < 256)
    {a b : ℝ} (hat : At y h.hia h.hib a b) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hT : 2 ^ h.mS * a + b = 2 ^ h.mS * C.t i j) (hR : (P.eR2d : ℝ) * a ^ 2 ≤ P.eR2n)
    (hS : (h.aS2d : ℝ) * b ^ 2 ≤ h.aS2n) (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * C.t i j)
    (hhi : (h.hid : ℝ) * C.t i j ≤ (h.hip : ℝ) - h.hin) : MinoFacts P C i j h y a b := by
  have hbiv : minoBiv h = true := by
    unfold minoBiv
    rcases hk with hk | hk <;> rw [hk] <;> rfl
  have hM : minoMM h = h.mS := by
    unfold minoMM
    rw [hbiv]
    rfl
  refine
    { hm0 := fun W L _ => recHm_form0 hf0 hcodes hat _ _ W L
      hm1 := fun W L hb0 => by
        rw [hf0] at hb0
        exact absurd hb0 (by decide)
      mcube := ⟨ha, hb⟩
      mT := fun W L => ?_
      mlocs := fun W L => ?_
      mcodes := hcodes }
  · unfold minoT
    rw [hbiv, hM]
    show ((Nat.shiftLeft 1 h.mS : ℕ) : ℝ) * var (realOps W L ![a, b, 0, 0, 0]) 0 + var (realOps W L ![a, b, 0, 0, 0]) 1 = _
    rw [vec0, vec1, cast_shl1]
    exact hT
  · intro g hg
    unfold minoLocs at hg
    rw [hbiv, hM] at hg
    have hg' : g ∈ [((1 : ℕ) : ℝ),
        (P.eR2n : ℝ) - (P.eR2d : ℝ) * (var (realOps W L ![a, b, 0, 0, 0]) 0 * var (realOps W L ![a, b, 0, 0, 0]) 0),
        (h.aS2n : ℝ) - (h.aS2d : ℝ) * (var (realOps W L ![a, b, 0, 0, 0]) 1 * var (realOps W L ![a, b, 0, 0, 0]) 1),
        locT (realOps W L ![a, b, 0, 0, 0]) h (2 ^ h.mS * C.t i j) h.mS] := hg
    rw [vec0, vec1] at hg'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl
    · simp
    · rw [← sq]
      linarith
    · rw [← sq]
      linarith
    · exact locT_nonneg h h.mS hlo hhi

/-- **The minorant of a ring type**, a polynomial in the last coordinate of the record. -/
theorem mino_k5 {h : RecH} (hk : h.kind = 5) (hf0 : h.hform = 0) (hcodes : ∀ c ∈ h.hex, c < 256) {a b : ℝ}
    (hat : At y h.hia h.hib a b) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hT : (h.c0p : ℝ) + 2 ^ h.jd * a - h.c0n = 2 ^ h.mTr * C.t i j)
    (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * C.t i j) (hhi : (h.hid : ℝ) * C.t i j ≤ (h.hip : ℝ) - h.hin) :
    MinoFacts P C i j h y a b := by
  have hbiv : minoBiv h = false := by
    unfold minoBiv
    rw [hk]
    rfl
  have hM : minoMM h = h.mTr := by
    unfold minoMM
    rw [hbiv, hf0]
    rfl
  refine
    { hm0 := fun W L _ => recHm_form0 hf0 hcodes hat _ _ W L
      hm1 := fun W L hb0 => by
        rw [hf0] at hb0
        exact absurd hb0 (by decide)
      mcube := ⟨ha, hb⟩
      mT := fun W L => ?_
      mlocs := fun W L => by
        rw [hM]
        exact minoLocs_uni hbiv _ hlo hhi W L _
      mcodes := hcodes }
  unfold minoT
  rw [hbiv, hf0, hM]
  show ((h.c0p : ℕ) : ℝ) + ((Nat.shiftLeft 1 h.jd : ℕ) : ℝ) * var (realOps W L ![a, b, 0, 0, 0]) 0 - ((h.c0n : ℕ) : ℝ) = _
  rw [vec0, cast_shl1]
  exact hT

/-! ## The kind AA: the pair of the labels `0`, `1` -/

theorem facts_k0 (lab : LabOk P heads) (hin : InPiece P heads C) :
    ∃ m0 m1, RecFacts P heads C 0 1 (hdOf P heads 0 1) (dpt P heads C 0 1) 1 1 m0 m1 := by
  have hp := lab.pair 0 1 (by norm_num) (by norm_num)
  have hmem := pairOk_mem hp
  have hk := pair_k0 hp (le_refl 1)
  obtain ⟨hform, hk0, -, -, -, -, -⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hs1, hc2, hs2⟩ := hk0 hk
  obtain ⟨hp1, hp2, hF0, -⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, -, hid1, -, -, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv 0 1 (by norm_num) (by norm_num)
  have hf0 : (hdOf P heads 0 1).hform ≠ 0 := by
    intro h0
    rcases (hF0 h0).2 with h | h | h <;> omega
  obtain ⟨m0, m1, M⟩ : ∃ m0 m1, MinoFacts P C 0 1 (hdOf P heads 0 1) (dpt P heads C 0 1) m0 m1 :=
    ⟨_, _, mino_h1 hform hrng hf0 ivlo ivhi (dpt P heads C 0 1)⟩
  obtain ⟨fu, fv, fx, fe⟩ := hin.frameA
  have hfP : fP 0 1 = 1 := fP_lt4 (by norm_num)
  have hfQ : fQ 0 1 = 1 := by
    rw [fQ_A (i := 0) (j := 1) (by norm_num)]
    norm_num
  have hcp : cp P C 1 = cp P C 0 := by
    unfold cp
    rw [if_pos (by norm_num), if_pos (by norm_num), eps0, eps1, fu]
    ring
  have hcq : cq P C 1 = cq P C 0 := by
    unfold cq
    rw [if_pos (by norm_num), if_pos (by norm_num), fv]
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 0 1)) 0 = cp P C 0 := fun W L => by
    rw [var0]
    show fP 0 1 * cp P C 0 = _
    rw [hfP, one_mul]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 0 1)) 1 = 1 * cq P C 0 := fun W L => by
    rw [var1]
    show fQ 0 1 * cq P C 0 = _
    rw [hfQ]
  have E1 := fun (W : ℕ) (L : Lay) => endA (W := W) (L := L) (y := dpt P heads C 0 1) (l := 0) (by norm_num)
    (hin.pairA 0 (by norm_num)) (τ := 1) (by norm_num) (hy0 W L) (hy1 W L) 0
  have E2 := fun (W : ℕ) (L : Lay) => endA (W := W) (L := L) (y := dpt P heads C 0 1) (l := 1) (by norm_num)
    (hin.pairA 1 (by norm_num)) (τ := 1) (by norm_num) (ip := 0) (iq := 1) (by rw [hy0 W L, hcp])
    (by rw [hy1 W L, hcq]) 1
  have hi2 := i2_k0 hk
  have hat2 : At (dpt P heads C 0 1) 0 1 ((-1) ^ 0 * cp P C 1) ((-1) ^ 0 * cq P C 1) := by
    have h := at01 (dpt P heads C 0 1)
    have e0 : dpt P heads C 0 1 0 = (-1) ^ 0 * cp P C 1 := by
      show fP 0 1 * cp P C 0 = _
      rw [hfP, hcp]
      ring
    have e1 : dpt P heads C 0 1 1 = (-1) ^ 0 * cq P C 1 := by
      show fQ 0 1 * cq P C 0 = _
      rw [hfQ, hcq]
      ring
    rw [e0, e1] at h
    exact h
  refine ⟨m0, m1, ?_⟩
  exact
    { cube := dpt_cube lab hin (by norm_num) (by norm_num) (by
        unfold lastV
        simp)
      su := by norm_num
      sv := by norm_num
      unit_i := hin.unit 0 (by norm_num)
      unit_j := hin.unit 1 (by norm_num)
      U1 := fun W L => by
        rw [hc1, hs1, (E1 W L).1, sgA0, eps0]
        ring
      V1 := fun W L => by rw [hc1, hs1, (E1 W L).2.1]
      U2 := fun W L => by
        rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).1, sgA1, eps1]
        ring
      V2 := fun W L => by rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).2.1]
      T := fun W L => by
        rw [recT_k0 hk, recMT_k0 hk]
        unfold Conf.t
        rw [fu, fv, fx, fe]
        linear_combination (-(2 ^ (2 * clsM P (hdOf P heads 0 1).c1))) * hin.unit 0 (by norm_num)
      loc1 := fun W L => by
        rw [hc1]
        exact (E1 W L).2.2
      loc2 := fun W L => by
        rw [hc2, hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      locD := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hc1, hs1, hc2, hs2, hi2.1, hi2.2]
        refine inner_cov (c1 := 0) (s1 := 0) (c2 := 0) (s2 := 1) (tp1 := flipP 0 1) (tq1 := flipQ 0 1) (tp2 := 0)
          (tq2 := 0) lab.kb lab.c0 lab.c1 (at01 _) hat2 (fun _ => flipP_lt4 (by norm_num)) (fun _ => rfl) ?_ W L
        intro blk _ _
        rw [lab.s0, lab.s1, chiF0, chiF0, flipQ_A (i := 0) (j := 1) (by norm_num)]
        simp
      pi1 := pi1_fact (by norm_num) hp1
      pi2 := fun W L => by
        rw [hi2.1, hi2.2, dotS_real0 (at01 _) P.wP _ hp2]
        unfold piN
        rw [if_neg (by norm_num), headOf_gt (by norm_num : 0 < 1)]
        show poly2 P.wP _ _ _ (fP 0 1 * cp P C 0) (fQ 0 1 * cq P C 0) = poly2 P.wP _ _ _ (fP 1 0 * cp P C 1) (fQ 1 0 * cq P C 1)
        rw [hfP, hfQ, hcp, hcq, fP_lt4 (i := 1) (j := 0) (by norm_num), fQ_A (i := 1) (j := 0) (by norm_num)]
        norm_num
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

/-! ## The kind BB: the pair of the labels `2`, `3` -/

theorem facts_k1 (lab : LabOk P heads) (hin : InPiece P heads C) :
    ∃ m0 m1, RecFacts P heads C 2 3 (hdOf P heads 2 3) (dpt P heads C 2 3) 1 1 m0 m1 := by
  have hp := lab.pair 2 3 (by norm_num) (by norm_num)
  have hmem := pairOk_mem hp
  have hk := pair_k1 hp (le_refl 2) (by norm_num) (le_refl 3)
  obtain ⟨hform, -, hk1, -, -, -, -⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hs1, hc2, hs2⟩ := hk1 hk
  obtain ⟨hp1, hp2, hF0, -⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, -, hid1, -, -, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv 2 3 (by norm_num) (by norm_num)
  have hf0 : (hdOf P heads 2 3).hform ≠ 0 := by
    intro h0
    rcases (hF0 h0).2 with h | h | h <;> omega
  obtain ⟨m0, m1, M⟩ : ∃ m0 m1, MinoFacts P C 2 3 (hdOf P heads 2 3) (dpt P heads C 2 3) m0 m1 :=
    ⟨_, _, mino_h1 hform hrng hf0 ivlo ivhi (dpt P heads C 2 3)⟩
  obtain ⟨fx, fe⟩ := hin.frameB
  have hfP : fP 2 3 = 1 := fP_lt4 (by norm_num)
  have hfQ : fQ 2 3 = 1 := by
    rw [fQ_B (i := 2) (j := 3) (by norm_num) (by norm_num)]
    norm_num
  have hfP' : fP 3 2 = 1 := fP_lt4 (by norm_num)
  have hfQ' : fQ 3 2 = 1 := by
    rw [fQ_B (i := 3) (j := 2) (by norm_num) (by norm_num)]
    norm_num
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 2 3)) 0 = cp P C 2 := fun W L => by
    rw [var0]
    show fP 2 3 * cp P C 2 = _
    rw [hfP, one_mul]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 2 3)) 1 = 1 * cq P C 2 := fun W L => by
    rw [var1]
    show fQ 2 3 * cq P C 2 = _
    rw [hfQ]
  have hy2 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 2 3)) 2 = cp P C 3 := fun W L => by
    rw [var2]
    show fP 3 2 * cp P C 3 = _
    rw [hfP', one_mul]
  have hy3 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C 2 3)) 3 = 1 * cq P C 3 := fun W L => by
    rw [var3]
    show fQ 3 2 * cq P C 3 = _
    rw [hfQ']
  have E1 := fun (W : ℕ) (L : Lay) => endB (W := W) (L := L) (y := dpt P heads C 2 3) (l := 2) (le_refl 2) (by norm_num)
    (hin.pairB 2 (le_refl 2) (by norm_num)) (τ := 1) (by norm_num) (hy0 W L) (hy1 W L) 0
  have E2 := fun (W : ℕ) (L : Lay) => endB (W := W) (L := L) (y := dpt P heads C 2 3) (l := 3) (by norm_num) (by norm_num)
    (hin.pairB 3 (by norm_num) (by norm_num)) (τ := 1) (by norm_num) (hy2 W L) (hy3 W L) 1
  have hi2 := i2_ne0 (h := hdOf P heads 2 3) (by omega)
  have h2 := hin.unit 2 (by norm_num)
  have h3 := hin.unit 3 (by norm_num)
  rw [fx, fe] at h3
  refine ⟨m0, m1, ?_⟩
  exact
    { cube := dpt_cube lab hin (by norm_num) (by norm_num) (by
        unfold lastV
        simp)
      su := by norm_num
      sv := by norm_num
      unit_i := hin.unit 2 (by norm_num)
      unit_j := hin.unit 3 (by norm_num)
      U1 := fun W L => by rw [hc1, hs1, (E1 W L).1]
      V1 := fun W L => by
        rw [hc1, hs1, (E1 W L).2.1, sgA0, eps2]
        ring
      U2 := fun W L => by rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).1]
      V2 := fun W L => by
        rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).2.1, sgA1, eps3]
        ring
      T := fun W L => by
        rw [recT_k1 hk, recMT_k1 hk, hc1, hc2]
        unfold Conf.t
        rw [fx, fe]
        linear_combination (-(2 ^ (2 * clsM P 1))) * h2 - (2 ^ (2 * clsM P 1)) * h3
      loc1 := fun W L => by
        rw [hc1]
        exact (E1 W L).2.2
      loc2 := fun W L => by
        rw [hc2, hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      locD := fun _ => by
        refine ⟨by rw [hc1, hc2], ?_, ?_⟩
        · unfold Conf.R
          rw [fx, fe]
        · rw [one_mul, one_mul, one_mul, one_mul]
          exact hin.dir
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hc1, hs1, hc2, hs2, hi2.1, hi2.2]
        refine inner_cov (c1 := 1) (s1 := 0) (c2 := 1) (s2 := 1) (tp1 := flipP 2 3) (tq1 := flipQ 2 3)
          (tp2 := flipP 3 2) (tq2 := flipQ 3 2) lab.kb lab.c2 lab.c3 (at01 _) (at23 _)
          (fun _ => flipP_lt4 (by norm_num)) (fun _ => flipP_lt4 (by norm_num)) ?_ W L
        intro blk _ _
        rw [lab.s2, lab.s3, chiF1, chiF1, flipQ_B (i := 2) (j := 3) (by norm_num) (by norm_num),
          flipQ_B (i := 3) (j := 2) (by norm_num) (by norm_num)]
        simp
      pi1 := pi1_fact (by norm_num) hp1
      pi2 := pi2_fact (by norm_num) (by omega) hp2
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

theorem sq_le_one_of_scaled {d n x : ℝ} (h : d * x ^ 2 ≤ n) (hn : n ≤ d) (hd : 1 ≤ d) : x ^ 2 ≤ 1 := by
  by_contra hc
  rw [not_le] at hc
  nlinarith [mul_pos (lt_of_lt_of_le zero_lt_one hd) (sub_pos.2 hc)]

theorem sgFlip0 : sgFlip 0 = 0 := rfl

theorem sgFlip1 : sgFlip 1 = 2 := rfl

theorem sgFlip2 : sgFlip 2 = 1 := rfl

/-! ## The kind AB: a label of the pair A and a label of the pair B -/

theorem facts_k2 (lab : LabOk P heads) (hin : InPiece P heads C) (hi : i ≤ 1) (hj2 : 2 ≤ j) (hj : j ≤ 3) :
    ∃ m0 m1, RecFacts P heads C i j (hdOf P heads i j) (dpt P heads C i j) (eps i) (eps j) m0 m1 := by
  have hij : i < j := by omega
  have hj9 : j < 9 := by omega
  have hp := lab.pair i j hij hj9
  have hmem := pairOk_mem hp
  have hk := pair_k2 hp hi hj2 hj
  obtain ⟨hform, -, -, hk2, -, -, -⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hs1, hc2, hs2⟩ := hk2 hk
  obtain ⟨hp1, hp2, hF0, -⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, -, hid1, -, hS2, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv i j hij hj9
  have hf0 : (hdOf P heads i j).hform ≠ 0 := by
    intro h0
    rcases (hF0 h0).2 with h | h | h <;> omega
  obtain ⟨m0, m1, M⟩ : ∃ m0 m1, MinoFacts P C i j (hdOf P heads i j) (dpt P heads C i j) m0 m1 :=
    ⟨_, _, mino_h1 hform hrng hf0 ivlo ivhi (dpt P heads C i j)⟩
  have hfP : fP i j = 1 := fP_lt4 (by omega)
  have hfQ : fQ i j = eps j := by
    rw [fQ_A hi]
    unfold eps
    obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
    · norm_num
    · norm_num
  have hfP' : fP j i = 1 := fP_lt4 (by omega)
  have hfQ' : fQ j i = eps i := by
    rw [fQ_B hj2 hj]
    unfold eps
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · norm_num
    · norm_num
  have hlastV : lastV P heads C i j = 2 ^ (hdOf P heads i j).mS * dev C i j := by
    unfold lastV
    rw [if_neg (by omega), if_pos (by omega)]
  have hdev : dev C i j = C.t i j - eps j * C.v i - eps i * C.u j := by
    unfold dev
    rw [if_pos (by omega), if_pos (by omega)]
  have hS : ((hdOf P heads i j).aS2d : ℝ) * lastV P heads C i j ^ 2 ≤ (hdOf P heads i j).aS2n := by
    rw [hlastV]
    exact hin.sdev i j hij hj9 (by omega) hj2 (Or.inl (by omega))
  obtain ⟨hSa, hSb⟩ := hS2 (by omega) (by omega)
  have hlast : |lastV P heads C i j| ≤ 1 := abs_le_one_of_sq (sq_le_one_of_scaled hS hSa hSb)
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 0 = cp P C i := fun W L => by
    rw [var0]
    show fP i j * cp P C i = _
    rw [hfP, one_mul]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 1 = eps j * cq P C i := fun W L => by
    rw [var1]
    show fQ i j * cq P C i = _
    rw [hfQ]
  have hy2 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 2 = cp P C j := fun W L => by
    rw [var2]
    show fP j i * cp P C j = _
    rw [hfP', one_mul]
  have hy3 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 3 = eps i * cq P C j := fun W L => by
    rw [var3]
    show fQ j i * cq P C j = _
    rw [hfQ']
  have E1 := fun (W : ℕ) (L : Lay) => endA (W := W) (L := L) (y := dpt P heads C i j) (l := i) (by omega)
    (hin.pairA i (by omega)) (τ := eps j) (eps_sq j) (hy0 W L) (hy1 W L) 0
  have E2 := fun (W : ℕ) (L : Lay) => endB (W := W) (L := L) (y := dpt P heads C i j) (l := j) hj2 (by omega)
    (hin.pairB j hj2 (by omega)) (τ := eps i) (eps_sq i) (hy2 W L) (hy3 W L) 0
  have hi2 := i2_ne0 (h := hdOf P heads i j) (by omega)
  have hdi : nth P.dcls i = 0 := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact lab.c0
    · exact lab.c1
  have hdj : nth P.dcls j = 1 := by
    obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
    · exact lab.c2
    · exact lab.c3
  have hsi : nth P.dsg i = i := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact lab.s0
    · exact lab.s1
  have hsj : nth P.dsg j = j - 2 := by
    obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
    · exact lab.s2
    · exact lab.s3
  refine ⟨m0, m1, ?_⟩
  exact
    { cube := dpt_cube lab hin (by omega) hj9 hlast
      su := eps_sq i
      sv := eps_sq j
      unit_i := hin.unit i (by omega)
      unit_j := hin.unit j hj9
      U1 := fun W L => by
        rw [hc1, hs1, (E1 W L).1, sgA0]
        ring
      V1 := fun W L => by rw [hc1, hs1, (E1 W L).2.1]
      U2 := fun W L => by rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).1]
      V2 := fun W L => by
        rw [hc2, hs2, hi2.1, hi2.2, (E2 W L).2.1, sgA0]
        ring
      T := fun W L => by
        rw [recT_k2 hk, recMT_k2 hk, var4]
        show _ * lastV P heads C i j + _ = _
        rw [hlastV, hdev]
        ring
      loc1 := fun W L => by
        rw [hc1]
        exact (E1 W L).2.2
      loc2 := fun W L => by
        rw [hc2, hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun _ => hS
      locD := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hc1, hs1, hc2, hs2, hi2.1, hi2.2]
        refine inner_cov (c1 := 0) (s1 := 0) (c2 := 1) (s2 := 0) (tp1 := flipP i j) (tq1 := flipQ i j)
          (tp2 := flipP j i) (tq2 := flipQ j i) lab.kb hdi hdj (at01 _) (at23 _) (fun _ => flipP_lt4 (by omega))
          (fun _ => flipP_lt4 (by omega)) ?_ W L
        intro blk hb1 hb2
        obtain ⟨hbb, -⟩ := hb1.1 rfl
        obtain ⟨hba, -⟩ := hb2.2.1 rfl
        rw [sgnR_sgnOf0, sgnR_sgnOf1, sgnR_sgnOf0, sgnR_sgnOf1, chiF0, chiF1, flipQ_A hi, flipQ_B hj2 hj, hsi, hsj]
        have ha : blk.a = 0 ∨ blk.a = 1 := by omega
        have hb : blk.b = 0 ∨ blk.b = 1 := by omega
        have hi' : i = 0 ∨ i = 1 := by omega
        have hj' : j = 2 ∨ j = 3 := by omega
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hi' with rfl | rfl <;>
          rcases hj' with rfl | rfl <;> simp [ha, hb]
      pi1 := pi1_fact hij hp1
      pi2 := pi2_fact hij (by omega) hp2
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

/-! ## The kind A r: a label of the pair A and a ring label -/

theorem facts_k3 (lab : LabOk P heads) (hin : InPiece P heads C) (hi : i ≤ 1) (hj4 : 4 ≤ j) (hj9 : j < 9) :
    ∃ m0 m1, RecFacts P heads C i j (hdOf P heads i j) (dpt P heads C i j) (eps i) 1 m0 m1 := by
  have hij : i < j := by omega
  have hp := lab.pair i j hij hj9
  have hmem := pairOk_mem hp
  obtain ⟨hk, hc2j⟩ := pair_k3 hp hi hj4
  obtain ⟨hform, -, -, -, hk3, -, -⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hs1, hc2⟩ := hk3 hk
  obtain ⟨hp1, hp2, hF0, hF1⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, -, hid1, -, hS2, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv i j hij hj9
  have hf0 : (hdOf P heads i j).hform = 0 := by
    by_contra h0
    exact (hF1 h0).2.2.1 hk
  obtain ⟨hcodes, hform3⟩ := hF0 hf0
  have hia : (hdOf P heads i j).hia = 2 ∧ (hdOf P heads i j).hib = 4 := by
    rcases hform3 with h | h | h
    · exact ⟨h.2.1, h.2.2⟩
    · omega
    · omega
  obtain ⟨r1, r2, r3, r4⟩ := hin.ring j hj4 hj9
  have hfP : fP i j = 1 := fP_lt4 (by omega)
  have hfQ : fQ i j = 1 := by rw [fQ_A hi, if_neg (by omega)]
  have hfP' : fP j i = eps i := by
    rw [fP_ring hj4]
    unfold eps
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · norm_num
    · norm_num
  have hfQ' : fQ j i = 1 := by rw [fQ_R hj4, if_neg (by omega)]
  have hcpj : cp P C j = C.u j := by
    unfold cp
    rw [if_neg (by omega), if_neg (by omega)]
  have hlastV : lastV P heads C i j = 2 ^ (hdOf P heads i j).mS * dev C i j := by
    unfold lastV
    rw [if_neg (by omega), if_pos (by omega)]
  have hdev : dev C i j = C.t i j - eps i * C.u j := by
    unfold dev
    rw [if_pos (by omega), if_neg (by omega)]
  have hS : ((hdOf P heads i j).aS2d : ℝ) * lastV P heads C i j ^ 2 ≤ (hdOf P heads i j).aS2n := by
    rw [hlastV]
    exact hin.sdev i j hij hj9 (by omega) (by omega) (Or.inl (by omega))
  obtain ⟨hSa, hSb⟩ := hS2 (by omega) (by omega)
  have hlast : |lastV P heads C i j| ≤ 1 := abs_le_one_of_sq (sq_le_one_of_scaled hS hSa hSb)
  have hcube := dpt_cube lab hin (by omega : i < 9) hj9 hlast
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 0 = cp P C i := fun W L => by
    rw [var0]
    show fP i j * cp P C i = _
    rw [hfP, one_mul]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 1 = 1 * cq P C i := fun W L => by
    rw [var1]
    show fQ i j * cq P C i = _
    rw [hfQ]
  have hy2 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 2 = eps i * cp P C j := fun W L => by
    rw [var2]
    show fP j i * cp P C j = _
    rw [hfP']
  have hy3 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 3 = 1 * cq P C j := fun W L => by
    rw [var3]
    show fQ j i * cq P C j = _
    rw [hfQ']
  have E1 := fun (W : ℕ) (L : Lay) => endA (W := W) (L := L) (y := dpt P heads C i j) (l := i) (by omega)
    (hin.pairA i (by omega)) (τ := 1) (by norm_num) (hy0 W L) (hy1 W L) 0
  have E2 := fun (W : ℕ) (L : Lay) => endR (W := W) (L := L) (y := dpt P heads C i j) (l := j)
    (cls := (hdOf P heads i j).c2) hj4 hc2 r1 r2 r3 (by rw [hc2j]; exact r4) (τp := eps i) (τq := 1) (eps_sq i)
    (by norm_num) (hy2 W L) (hy3 W L) (hdOf P heads i j).s2
  have hi2 := i2_ne0 (h := hdOf P heads i j) (by omega)
  have hm2 : clsM P (hdOf P heads i j).c2 = 0 := clsM_ring hc2
  have hdi : nth P.dcls i = 0 := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact lab.c0
    · exact lab.c1
  have hsi : nth P.dsg i = i := by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · exact lab.s0
    · exact lab.s1
  have hat : At (dpt P heads C i j) (hdOf P heads i j).hia (hdOf P heads i j).hib (dpt P heads C i j 2)
      (dpt P heads C i j 4) := by
    rw [hia.1, hia.2]
    exact at24 _
  have M : MinoFacts P C i j (hdOf P heads i j) (dpt P heads C i j) (dpt P heads C i j 2) (dpt P heads C i j 4) :=
    mino_biv (Or.inl hk) hf0 hcodes hat (hcube 2) (hcube 4)
      (by
        show 2 ^ _ * (fP j i * cp P C j) + lastV P heads C i j = _
        rw [hfP', hcpj, hlastV, hdev]
        ring)
      (by
        show _ * (fP j i * cp P C j) ^ 2 ≤ _
        rw [hfP', hcpj, mul_pow, eps_sq, one_mul]
        exact r1)
      hS ivlo ivhi
  refine ⟨dpt P heads C i j 2, dpt P heads C i j 4, ?_⟩
  exact
    { cube := hcube
      su := eps_sq i
      sv := by norm_num
      unit_i := hin.unit i (by omega)
      unit_j := hin.unit j hj9
      U1 := fun W L => by
        rw [hc1, hs1, (E1 W L).1, sgA0]
        ring
      V1 := fun W L => by rw [hc1, hs1, (E1 W L).2.1]
      U2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).1]
      V2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).2.1]
      T := fun W L => by
        rw [recT_k3 hk, recMT_k3 hk, var4]
        show lastV P heads C i j + _ = _
        rw [hlastV, hdev, hm2]
        ring
      loc1 := fun W L => by
        rw [hc1]
        exact (E1 W L).2.2
      loc2 := fun W L => by
        rw [hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun _ => hS
      locD := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hc1, hs1, hi2.1, hi2.2]
        refine inner_cov (c1 := 0) (s1 := 0) (c2 := (hdOf P heads i j).c2) (s2 := (hdOf P heads i j).s2)
          (tp1 := flipP i j) (tq1 := flipQ i j) (tp2 := flipP j i) (tq2 := flipQ j i) lab.kb hdi hc2j.symm (at01 _)
          (at23 _) (fun _ => flipP_lt4 (by omega)) (fun hlt => absurd hlt (by omega)) ?_ W L
        intro blk hb1 hb2
        obtain ⟨hbb, hodd⟩ := hb1.1 rfl
        obtain ⟨hba, -⟩ := hb2.2.2 hc2
        have hodd1 : blk.odd ≠ 1 := by omega
        have hj3 : j ≠ 3 := by omega
        rw [sgnR_sgnOf0, sgnR_ring_even hc2 _ hodd1, sgnR_sgnOf0, sgnR_ring_even hc2 _ hodd1, chiF0, chiF_ring hc2,
          flipQ_A hi, flipP_ring hj4, flipQ_R hj4, hsi, if_neg hj3]
        have ha : blk.a = 0 ∨ blk.a = 1 := by omega
        have hi' : i = 0 ∨ i = 1 := by omega
        rcases ha with ha | ha <;> rcases hi' with rfl | rfl <;> simp [ha]
      pi1 := pi1_fact hij hp1
      pi2 := pi2_fact hij (by omega) hp2
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

/-! ## The kind B r: a label of the pair B and a ring label -/

theorem facts_k4 (lab : LabOk P heads) (hin : InPiece P heads C) (hi2' : 2 ≤ i) (hi : i ≤ 3) (hj4 : 4 ≤ j)
    (hj9 : j < 9) :
    ∃ m0 m1, RecFacts P heads C i j (hdOf P heads i j) (dpt P heads C i j) 1 (eps i) m0 m1 := by
  have hij : i < j := by omega
  have hp := lab.pair i j hij hj9
  have hmem := pairOk_mem hp
  obtain ⟨hk, hc2j⟩ := pair_k4 hp hi2' hi hj4
  obtain ⟨hform, -, -, -, -, hk4, -⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hs1, hc2⟩ := hk4 hk
  obtain ⟨hp1, hp2, hF0, hF1⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, -, hid1, -, hS2, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv i j hij hj9
  have hf0 : (hdOf P heads i j).hform = 0 := by
    by_contra h0
    exact (hF1 h0).2.2.2 hk
  obtain ⟨hcodes, hform3⟩ := hF0 hf0
  have hia : (hdOf P heads i j).hia = 3 ∧ (hdOf P heads i j).hib = 4 := by
    rcases hform3 with h | h | h
    · omega
    · exact ⟨h.2.1, h.2.2⟩
    · omega
  obtain ⟨r1, r2, r3, r4⟩ := hin.ring j hj4 hj9
  have hfP : fP i j = 1 := fP_lt4 (by omega)
  have hfQ : fQ i j = 1 := by rw [fQ_B hi2' hi, if_neg (by omega)]
  have hfP' : fP j i = 1 := by rw [fP_ring hj4, if_neg (by omega)]
  have hfQ' : fQ j i = eps i := by
    rw [fQ_R hj4]
    unfold eps
    obtain rfl | rfl : i = 2 ∨ i = 3 := by omega
    · norm_num
    · norm_num
  have hcqj : cq P C j = C.v j := by
    unfold cq
    rw [if_neg (by omega), if_neg (by omega)]
  have hlastV : lastV P heads C i j = 2 ^ (hdOf P heads i j).mS * dev C i j := by
    unfold lastV
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hdev : dev C i j = C.t i j - eps i * C.v j := by
    unfold dev
    rw [if_neg (by omega)]
  have hS : ((hdOf P heads i j).aS2d : ℝ) * lastV P heads C i j ^ 2 ≤ (hdOf P heads i j).aS2n := by
    rw [hlastV]
    exact hin.sdev i j hij hj9 (by omega) (by omega) (Or.inr hj4)
  obtain ⟨hSa, hSb⟩ := hS2 (by omega) (by omega)
  have hlast : |lastV P heads C i j| ≤ 1 := abs_le_one_of_sq (sq_le_one_of_scaled hS hSa hSb)
  have hcube := dpt_cube lab hin (by omega : i < 9) hj9 hlast
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 0 = cp P C i := fun W L => by
    rw [var0]
    show fP i j * cp P C i = _
    rw [hfP, one_mul]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 1 = 1 * cq P C i := fun W L => by
    rw [var1]
    show fQ i j * cq P C i = _
    rw [hfQ]
  have hy2 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 2 = 1 * cp P C j := fun W L => by
    rw [var2]
    show fP j i * cp P C j = _
    rw [hfP']
  have hy3 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 3 = eps i * cq P C j := fun W L => by
    rw [var3]
    show fQ j i * cq P C j = _
    rw [hfQ']
  have E1 := fun (W : ℕ) (L : Lay) => endB (W := W) (L := L) (y := dpt P heads C i j) (l := i) hi2' (by omega)
    (hin.pairB i hi2' (by omega)) (τ := 1) (by norm_num) (hy0 W L) (hy1 W L) 0
  have E2 := fun (W : ℕ) (L : Lay) => endR (W := W) (L := L) (y := dpt P heads C i j) (l := j)
    (cls := (hdOf P heads i j).c2) hj4 hc2 r1 r2 r3 (by rw [hc2j]; exact r4) (τp := 1) (τq := eps i) (by norm_num)
    (eps_sq i) (hy2 W L) (hy3 W L) (hdOf P heads i j).s2
  have hi2 := i2_ne0 (h := hdOf P heads i j) (by omega)
  have hm2 : clsM P (hdOf P heads i j).c2 = 0 := clsM_ring hc2
  have hdi : nth P.dcls i = 1 := by
    obtain rfl | rfl : i = 2 ∨ i = 3 := by omega
    · exact lab.c2
    · exact lab.c3
  have hsi : nth P.dsg i = i - 2 := by
    obtain rfl | rfl : i = 2 ∨ i = 3 := by omega
    · exact lab.s2
    · exact lab.s3
  have hat : At (dpt P heads C i j) (hdOf P heads i j).hia (hdOf P heads i j).hib (dpt P heads C i j 3)
      (dpt P heads C i j 4) := by
    rw [hia.1, hia.2]
    exact at34 _
  have M : MinoFacts P C i j (hdOf P heads i j) (dpt P heads C i j) (dpt P heads C i j 3) (dpt P heads C i j 4) :=
    mino_biv (Or.inr hk) hf0 hcodes hat (hcube 3) (hcube 4)
      (by
        show 2 ^ _ * (fQ j i * cq P C j) + lastV P heads C i j = _
        rw [hfQ', hcqj, hlastV, hdev]
        ring)
      (by
        show _ * (fQ j i * cq P C j) ^ 2 ≤ _
        rw [hfQ', hcqj, mul_pow, eps_sq, one_mul]
        exact r2)
      hS ivlo ivhi
  refine ⟨dpt P heads C i j 3, dpt P heads C i j 4, ?_⟩
  exact
    { cube := hcube
      su := by norm_num
      sv := eps_sq i
      unit_i := hin.unit i (by omega)
      unit_j := hin.unit j hj9
      U1 := fun W L => by rw [hc1, hs1, (E1 W L).1]
      V1 := fun W L => by
        rw [hc1, hs1, (E1 W L).2.1, sgA0]
        ring
      U2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).1]
      V2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).2.1]
      T := fun W L => by
        rw [recT_k4 hk, recMT_k4 hk, var4]
        show lastV P heads C i j + _ = _
        rw [hlastV, hdev, hm2]
        ring
      loc1 := fun W L => by
        rw [hc1]
        exact (E1 W L).2.2
      loc2 := fun W L => by
        rw [hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun _ => hS
      locD := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hc1, hs1, hi2.1, hi2.2]
        refine inner_cov (c1 := 1) (s1 := 0) (c2 := (hdOf P heads i j).c2) (s2 := (hdOf P heads i j).s2)
          (tp1 := flipP i j) (tq1 := flipQ i j) (tp2 := flipP j i) (tq2 := flipQ j i) lab.kb hdi hc2j.symm (at01 _)
          (at23 _) (fun _ => flipP_lt4 (by omega)) (fun hlt => absurd hlt (by omega)) ?_ W L
        intro blk hb1 hb2
        obtain ⟨hba, hodd⟩ := hb1.2.1 rfl
        obtain ⟨-, hbb⟩ := hb2.2.2 hc2
        have hodd1 : blk.odd ≠ 1 := by omega
        have hj1 : j ≠ 1 := by omega
        have hi1' : i ≠ 1 := by omega
        rw [sgnR_sgnOf1, sgnR_ring_even hc2 _ hodd1, sgnR_sgnOf1, sgnR_ring_even hc2 _ hodd1, chiF1, chiF_ring hc2,
          flipQ_B hi2' hi, flipP_ring hj4, flipQ_R hj4, hsi, if_neg hj1, if_neg hi1']
        have hb : blk.b = 0 ∨ blk.b = 1 := by omega
        have hi' : i = 2 ∨ i = 3 := by omega
        rcases hb with hb | hb <;> rcases hi' with rfl | rfl <;> simp [hb]
      pi1 := pi1_fact hij hp1
      pi2 := pi2_fact hij (by omega) hp2
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

/-! ## The ring types: two ring labels -/

theorem facts_k5 (lab : LabOk P heads) (hin : InPiece P heads C) (hi4 : 4 ≤ i) (hij : i < j) (hj9 : j < 9) :
    ∃ m0 m1, RecFacts P heads C i j (hdOf P heads i j) (dpt P heads C i j) 1 1 m0 m1 := by
  have hp := lab.pair i j hij hj9
  have hmem := pairOk_mem hp
  obtain ⟨hk, hc1i, hc2j, hsg⟩ := pair_k5 hp hi4 hij
  obtain ⟨hform, -, -, -, -, -, hk5⟩ := headOk_real (lab.head _ hmem)
  obtain ⟨hc1, hc2, hs1le, hs2le⟩ := hk5 hk
  obtain ⟨hp1, hp2, hF0, hF1⟩ := formOk_real hform
  have hrng := lab.rng _ hmem
  obtain ⟨hi1, hlod, hid1, hI5, -, -⟩ := rangesOk_real hrng
  obtain ⟨ivlo, ivhi⟩ := hin.iv i j hij hj9
  obtain ⟨r1, r2, r3, r4⟩ := hin.ring i hi4 (by omega)
  obtain ⟨q1, q2, q3, q4⟩ := hin.ring j (by omega) hj9
  have hfP : fP i j = 1 := by rw [fP_ring hi4, if_neg (by omega)]
  have hfQ : fQ i j = 1 := by rw [fQ_R hi4, if_neg (by omega)]
  have hfP' : fP j i = 1 := by rw [fP_ring (by omega : 4 ≤ j), if_neg (by omega)]
  have hfQ' : fQ j i = 1 := by rw [fQ_R (by omega : 4 ≤ j), if_neg (by omega)]
  have hlastV : lastV P heads C i j
      = (2 ^ (hdOf P heads i j).mTr * C.t i j - (((hdOf P heads i j).c0p : ℝ) - (hdOf P heads i j).c0n))
        / 2 ^ (hdOf P heads i j).jd := by
    unfold lastV
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hlast : |lastV P heads C i j| ≤ 1 := by
    rw [hlastV]
    exact interval_real (hI5 hk) hlod hid1 ivlo ivhi
  have hcube := dpt_cube lab hin (by omega : i < 9) hj9 hlast
  have h2jd : (2 : ℝ) ^ (hdOf P heads i j).jd ≠ 0 := by positivity
  have hTT : ((hdOf P heads i j).c0p : ℝ) + 2 ^ (hdOf P heads i j).jd * lastV P heads C i j - (hdOf P heads i j).c0n
      = 2 ^ (hdOf P heads i j).mTr * C.t i j := by
    rw [hlastV, mul_div_assoc', mul_div_cancel_left₀ _ h2jd]
    ring
  have hy0 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 0 = 1 * cp P C i := fun W L => by
    rw [var0]
    show fP i j * cp P C i = _
    rw [hfP]
  have hy1 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 1 = 1 * cq P C i := fun W L => by
    rw [var1]
    show fQ i j * cq P C i = _
    rw [hfQ]
  have hy2 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 2 = 1 * cp P C j := fun W L => by
    rw [var2]
    show fP j i * cp P C j = _
    rw [hfP']
  have hy3 : ∀ (W : ℕ) (L : Lay), var (realOps W L (dpt P heads C i j)) 3 = 1 * cq P C j := fun W L => by
    rw [var3]
    show fQ j i * cq P C j = _
    rw [hfQ']
  have E1 := fun (W : ℕ) (L : Lay) => endR (W := W) (L := L) (y := dpt P heads C i j) (l := i)
    (cls := (hdOf P heads i j).c1) hi4 hc1 r1 r2 r3 (by rw [hc1i]; exact r4) (τp := 1) (τq := 1) (by norm_num)
    (by norm_num) (hy0 W L) (hy1 W L) (hdOf P heads i j).s1
  have E2 := fun (W : ℕ) (L : Lay) => endR (W := W) (L := L) (y := dpt P heads C i j) (l := j)
    (cls := (hdOf P heads i j).c2) (by omega) hc2 q1 q2 q3 (by rw [hc2j]; exact q4) (τp := 1) (τq := 1) (by norm_num)
    (by norm_num) (hy2 W L) (hy3 W L) (hdOf P heads i j).s2
  have hi2 := i2_ne0 (h := hdOf P heads i j) (by omega)
  have hM : ∃ m0 m1, MinoFacts P C i j (hdOf P heads i j) (dpt P heads C i j) m0 m1 := by
    by_cases hf0 : (hdOf P heads i j).hform = 0
    · obtain ⟨hcodes, hform3⟩ := hF0 hf0
      have hia : (hdOf P heads i j).hia = 4 ∧ (hdOf P heads i j).hib = 0 := by
        rcases hform3 with h | h | h
        · omega
        · omega
        · exact ⟨h.2.1, h.2.2⟩
      have hat : At (dpt P heads C i j) (hdOf P heads i j).hia (hdOf P heads i j).hib (dpt P heads C i j 4)
          (dpt P heads C i j 0) := by
        rw [hia.1, hia.2]
        exact at40 _
      exact ⟨_, _, mino_k5 hk hf0 hcodes hat (hcube 4) (hcube 0) hTT ivlo ivhi⟩
    · exact ⟨_, _, mino_h1 hform hrng hf0 ivlo ivhi (dpt P heads C i j)⟩
  obtain ⟨m0, m1, M⟩ := hM
  refine ⟨m0, m1, ?_⟩
  exact
    { cube := hcube
      su := by norm_num
      sv := by norm_num
      unit_i := hin.unit i (by omega)
      unit_j := hin.unit j hj9
      U1 := fun W L => (E1 W L).1
      V1 := fun W L => (E1 W L).2.1
      U2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).1]
      V2 := fun W L => by rw [hi2.1, hi2.2, (E2 W L).2.1]
      T := fun W L => by
        rw [recT_k5 hk, recMT_k5 hk, var4]
        exact hTT
      loc1 := fun W L => (E1 W L).2.2
      loc2 := fun W L => by
        rw [hi2.1, hi2.2]
        exact (E2 W L).2.2
      locS := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      locD := fun hb => by
        rw [hk] at hb
        exact absurd hb (by decide)
      hm0 := M.hm0
      hm1 := M.hm1
      inner := fun W L => by
        rw [hi2.1, hi2.2]
        refine inner_cov (c1 := (hdOf P heads i j).c1) (s1 := (hdOf P heads i j).s1) (c2 := (hdOf P heads i j).c2)
          (s2 := (hdOf P heads i j).s2) (tp1 := flipP i j) (tq1 := flipQ i j) (tp2 := flipP j i) (tq2 := flipQ j i)
          lab.kb hc1i.symm hc2j.symm (at01 _) (at23 _) (fun hlt => absurd hlt (by omega))
          (fun hlt => absurd hlt (by omega)) ?_ W L
        intro blk _ _
        have hj1 : j ≠ 1 := by omega
        have hj3 : j ≠ 3 := by omega
        have hi1' : i ≠ 1 := by omega
        have hi3 : i ≠ 3 := by omega
        rw [chiF_ring hc1, chiF_ring hc2, flipP_ring hi4, flipQ_R hi4, flipP_ring (i := j) (j := i) (by omega),
          flipQ_R (i := j) (j := i) (by omega), if_neg hj1, if_neg hj3, if_neg hi1', if_neg hi3]
        simp only [Nat.zero_mul, Nat.add_zero, pow_zero, mul_one]
        by_cases ho : blk.odd = 1
        · rw [sgnR_ring_odd hc1 _ ho, sgnR_ring_odd hc2 _ ho, sgnR_ring_odd hc1 _ ho, sgnR_ring_odd hc2 _ ho]
          rcases hsg with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · rw [e1, e2]
          · rw [e1, e2]
            have h1 : (hdOf P heads i j).s1 = 0 ∨ (hdOf P heads i j).s1 = 1 ∨ (hdOf P heads i j).s1 = 2 := by omega
            have h2 : (hdOf P heads i j).s2 = 0 ∨ (hdOf P heads i j).s2 = 1 ∨ (hdOf P heads i j).s2 = 2 := by omega
            rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> rw [h1, h2] <;>
              simp [sgFlip0, sgFlip1, sgFlip2]
        · rw [sgnR_ring_even hc1 _ ho, sgnR_ring_even hc2 _ ho, sgnR_ring_even hc1 _ ho, sgnR_ring_even hc2 _ ho]
      pi1 := pi1_fact hij hp1
      pi2 := pi2_fact hij (by omega) hp2
      mcube := M.mcube
      mT := M.mT
      mlocs := M.mlocs
      mcodes := M.mcodes
      ivlo := ivlo
      ivhi := ivhi
      hi1 := hi1
      hid1 := hid1 }

/-! ## All pairs -/

/-- **The facts of every pair of labels** of a configuration of the piece. -/
theorem rec_facts (hlab : labelsOk P heads = true) (hin : InPiece P heads C) (hij : i < j) (hj : j < 9) :
    ∃ y σu σv m0 m1, RecFacts P heads C i j (hdOf P heads i j) y σu σv m0 m1 := by
  have lab := labOk_of hlab
  by_cases h1 : j ≤ 1
  · obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 1 := by omega
    obtain ⟨m0, m1, F⟩ := facts_k0 lab hin
    exact ⟨_, _, _, m0, m1, F⟩
  by_cases h2 : i ≤ 1
  · by_cases h3 : j ≤ 3
    · obtain ⟨m0, m1, F⟩ := facts_k2 lab hin h2 (by omega) h3
      exact ⟨_, _, _, m0, m1, F⟩
    · obtain ⟨m0, m1, F⟩ := facts_k3 lab hin h2 (by omega) hj
      exact ⟨_, _, _, m0, m1, F⟩
  by_cases h4 : i ≤ 3
  · by_cases h3 : j ≤ 3
    · obtain ⟨rfl, rfl⟩ : i = 2 ∧ j = 3 := by omega
      obtain ⟨m0, m1, F⟩ := facts_k1 lab hin
      exact ⟨_, _, _, m0, m1, F⟩
    · obtain ⟨m0, m1, F⟩ := facts_k4 lab hin (by omega) h4 (by omega) hj
      exact ⟨_, _, _, m0, m1, F⟩
  · obtain ⟨m0, m1, F⟩ := facts_k5 lab hin (by omega) hij hj
    exact ⟨_, _, _, m0, m1, F⟩

end CAP.VR
