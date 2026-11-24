module

public import Mathlib.Data.Nat.ModEq
public import CAP.VR.Pair

/-!
# Virtual-root certificates: what the check of the labels gives, and the covariance of the kernel

* `LabOk`: the content of the check `labelsOk`; `pair_k0`, …, `pair_k5`: the kind of the record type of a pair.
* The signs `fP`, `fQ` of the class coordinates of a label in the data of a pair.
* `inner_cov`: the blocks of the kernel at the two end points of a record are those of the two labels. The
  features of a class have fixed parities (`exOk`), so a change of sign of a coordinate multiplies the columns
  of a block by a sign (`featL_flip`), and the signs of the two end points cancel.
* `MinoFacts`: the facts on the minorant of a pair; `mino_h1` for a minorant in the centred inner product.
* `cp_abs`: the class coordinates lie in `[-1, 1]`.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ} {P : Par} {heads : List RecH} {C : Conf} {i j : ℕ}

/-! ## The check of the labels -/

theorem ble_false {a b : ℕ} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) (by omega)

/-- The content of the check `labelsOk`. -/
structure LabOk (P : Par) (heads : List RecH) : Prop where
  c0 : nth P.dcls 0 = 0
  c1 : nth P.dcls 1 = 0
  c2 : nth P.dcls 2 = 1
  c3 : nth P.dcls 3 = 1
  s0 : nth P.dsg 0 = 0
  s1 : nth P.dsg 1 = 1
  s2 : nth P.dsg 2 = 0
  s3 : nth P.dsg 3 = 1
  ring : ∀ l, 4 ≤ l → l < 9 → 2 ≤ nth P.dcls l
  head : ∀ h ∈ heads, headOk h = true
  rng : ∀ h ∈ heads, rangesOk h = true
  consts : constsOk P = true
  pair : ∀ i j, i < j → j < 9 → pairOk P heads i j = true
  kb : kblocksOk P.kblocks = true

theorem labOk_of (h : labelsOk P heads = true) : LabOk P heads := by
  unfold labelsOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a0, a1⟩, a2⟩, a3⟩, b0⟩, b1⟩, b2⟩, b3⟩, _⟩, _⟩, hr⟩, hh⟩, hg⟩, hc⟩, hp⟩, hk⟩ := h
  exact
    { c0 := Nat.eq_of_beq_eq_true a0
      c1 := Nat.eq_of_beq_eq_true a1
      c2 := Nat.eq_of_beq_eq_true a2
      c3 := Nat.eq_of_beq_eq_true a3
      s0 := Nat.eq_of_beq_eq_true b0
      s1 := Nat.eq_of_beq_eq_true b1
      s2 := Nat.eq_of_beq_eq_true b2
      s3 := Nat.eq_of_beq_eq_true b3
      ring := fun l h4 h9 => by
        have h := allN_lt 9 hr l h9
        have h' : (Nat.ble l 3 || Nat.ble 2 (nth P.dcls l)) = true := h
        rw [Bool.or_eq_true] at h'
        rcases h' with h' | h'
        · exact absurd (Nat.le_of_ble_eq_true h') (by omega)
        · exact Nat.le_of_ble_eq_true h'
      head := allH_mem heads hh
      rng := allH_mem heads hg
      consts := hc
      pair := fun i j hij hj => allN_lt j (allN_lt 9 hp j hj) i hij
      kb := hk }

theorem pairOk_mem (hp : pairOk P heads i j = true) : hdOf P heads i j ∈ heads := by
  unfold pairOk at hp
  rw [Bool.and_eq_true] at hp
  exact nthH_mem heads _ (lt_of_blt hp.1)

theorem pairOk_cases (hp : pairOk P heads i j = true) :
    cond (Nat.ble j 1) (Nat.beq (hdOf P heads i j).kind 0)
      (cond (Nat.ble 2 i && Nat.ble j 3) (Nat.beq (hdOf P heads i j).kind 1)
        (cond (Nat.ble i 1 && Nat.ble j 3) (Nat.beq (hdOf P heads i j).kind 2)
          (cond (Nat.ble i 1) (Nat.beq (hdOf P heads i j).kind 3 && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j))
            (cond (Nat.ble i 3) (Nat.beq (hdOf P heads i j).kind 4 && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j))
              (Nat.beq (hdOf P heads i j).kind 5 && Nat.beq (hdOf P heads i j).c1 (nth P.dcls i)
                && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j)
                && ((Nat.beq (nth P.dsg i) (hdOf P heads i j).s1 && Nat.beq (nth P.dsg j) (hdOf P heads i j).s2)
                  || (Nat.beq (nth P.dsg i) (sgFlip (hdOf P heads i j).s1)
                    && Nat.beq (nth P.dsg j) (sgFlip (hdOf P heads i j).s2)))))))) = true := by
  unfold pairOk at hp
  rw [Bool.and_eq_true] at hp
  exact hp.2

theorem pair_k0 (hp : pairOk P heads i j = true) (hj : j ≤ 1) : (hdOf P heads i j).kind = 0 := by
  have h := pairOk_cases hp
  rw [Nat.ble_eq_true_of_le hj] at h
  exact Nat.eq_of_beq_eq_true h

theorem pair_k1 (hp : pairOk P heads i j = true) (hi : 2 ≤ i) (hij : i < j) (hj : j ≤ 3) :
    (hdOf P heads i j).kind = 1 := by
  have h := pairOk_cases hp
  rw [ble_false (by omega : 1 < j), Nat.ble_eq_true_of_le hi, Nat.ble_eq_true_of_le hj] at h
  exact Nat.eq_of_beq_eq_true h

theorem pair_k2 (hp : pairOk P heads i j = true) (hi : i ≤ 1) (hj2 : 2 ≤ j) (hj : j ≤ 3) :
    (hdOf P heads i j).kind = 2 := by
  have h := pairOk_cases hp
  rw [ble_false (by omega : 1 < j), ble_false (by omega : i < 2), Nat.ble_eq_true_of_le hi,
    Nat.ble_eq_true_of_le hj] at h
  exact Nat.eq_of_beq_eq_true h

theorem pair_k3 (hp : pairOk P heads i j = true) (hi : i ≤ 1) (hj : 4 ≤ j) :
    (hdOf P heads i j).kind = 3 ∧ (hdOf P heads i j).c2 = nth P.dcls j := by
  have h := pairOk_cases hp
  rw [ble_false (by omega : 1 < j), ble_false (by omega : i < 2), Nat.ble_eq_true_of_le hi,
    ble_false (by omega : 3 < j)] at h
  have h' : (Nat.beq (hdOf P heads i j).kind 3 && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j)) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩

theorem pair_k4 (hp : pairOk P heads i j = true) (hi2 : 2 ≤ i) (hi : i ≤ 3) (hj : 4 ≤ j) :
    (hdOf P heads i j).kind = 4 ∧ (hdOf P heads i j).c2 = nth P.dcls j := by
  have h := pairOk_cases hp
  rw [ble_false (by omega : 1 < j), Nat.ble_eq_true_of_le hi2, ble_false (by omega : 3 < j),
    ble_false (by omega : 1 < i), Nat.ble_eq_true_of_le hi] at h
  have h' : (Nat.beq (hdOf P heads i j).kind 4 && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j)) = true := h
  rw [Bool.and_eq_true] at h'
  exact ⟨Nat.eq_of_beq_eq_true h'.1, Nat.eq_of_beq_eq_true h'.2⟩

theorem pair_k5 (hp : pairOk P heads i j = true) (hi : 4 ≤ i) (hij : i < j) :
    (hdOf P heads i j).kind = 5 ∧ (hdOf P heads i j).c1 = nth P.dcls i ∧ (hdOf P heads i j).c2 = nth P.dcls j
      ∧ ((nth P.dsg i = (hdOf P heads i j).s1 ∧ nth P.dsg j = (hdOf P heads i j).s2)
        ∨ (nth P.dsg i = sgFlip (hdOf P heads i j).s1 ∧ nth P.dsg j = sgFlip (hdOf P heads i j).s2)) := by
  have h := pairOk_cases hp
  rw [ble_false (by omega : 1 < j), Nat.ble_eq_true_of_le (by omega : 2 ≤ i), ble_false (by omega : 3 < j),
    ble_false (by omega : 1 < i), ble_false (by omega : 3 < i)] at h
  have h' : (Nat.beq (hdOf P heads i j).kind 5 && Nat.beq (hdOf P heads i j).c1 (nth P.dcls i)
      && Nat.beq (hdOf P heads i j).c2 (nth P.dcls j)
      && ((Nat.beq (nth P.dsg i) (hdOf P heads i j).s1 && Nat.beq (nth P.dsg j) (hdOf P heads i j).s2)
        || (Nat.beq (nth P.dsg i) (sgFlip (hdOf P heads i j).s1)
          && Nat.beq (nth P.dsg j) (sgFlip (hdOf P heads i j).s2)))) = true := h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h'
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h'
  refine ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c, ?_⟩
  rcases d with d | d
  · exact Or.inl ⟨Nat.eq_of_beq_eq_true d.1, Nat.eq_of_beq_eq_true d.2⟩
  · exact Or.inr ⟨Nat.eq_of_beq_eq_true d.1, Nat.eq_of_beq_eq_true d.2⟩

/-! ## The signs of the class coordinates -/

theorem flipP_lt4 (hi : i < 4) : flipP i j = 0 := by
  unfold flipP
  rw [ble_false (by omega : i < 4)]
  rfl

theorem flipP_ring (hi : 4 ≤ i) : flipP i j = if j = 1 then 1 else 0 := by
  unfold flipP
  rw [Nat.ble_eq_true_of_le hi]
  by_cases h : j = 1
  · rw [h, if_pos rfl]
    rfl
  · rw [beq_false_of_ne h, if_neg h]
    rfl

theorem flipQ_A (hi : i ≤ 1) : flipQ i j = if j = 3 then 1 else 0 := by
  unfold flipQ
  rw [Nat.ble_eq_true_of_le hi, ble_false (by omega : i < 2), ble_false (by omega : i < 4)]
  by_cases h : j = 3
  · rw [h, if_pos rfl]
    rfl
  · rw [beq_false_of_ne h, if_neg h]
    rfl

theorem flipQ_B (hi2 : 2 ≤ i) (hi : i ≤ 3) : flipQ i j = if j = 1 then 1 else 0 := by
  unfold flipQ
  rw [ble_false (by omega : 1 < i), Nat.ble_eq_true_of_le hi2, Nat.ble_eq_true_of_le hi, ble_false (by omega : i < 4)]
  by_cases h : j = 1
  · rw [h, if_pos rfl]
    rfl
  · rw [beq_false_of_ne h, if_neg h]
    cases Nat.beq j 3 <;> rfl

theorem flipQ_R (hi : 4 ≤ i) : flipQ i j = if j = 3 then 1 else 0 := by
  unfold flipQ
  rw [ble_false (by omega : 1 < i), Nat.ble_eq_true_of_le (by omega : 2 ≤ i), ble_false (by omega : 3 < i),
    Nat.ble_eq_true_of_le hi]
  by_cases h : j = 3
  · rw [h, if_pos rfl]
    rfl
  · rw [beq_false_of_ne h, if_neg h]
    rfl

theorem eps0 : eps 0 = 1 := by
  unfold eps
  norm_num

theorem eps1 : eps 1 = -1 := by
  unfold eps
  norm_num

theorem eps2 : eps 2 = 1 := by
  unfold eps
  norm_num

theorem eps3 : eps 3 = -1 := by
  unfold eps
  norm_num

theorem eps_ring {l : ℕ} (hl : 4 ≤ l) : eps l = 1 := by
  unfold eps
  rw [if_neg (by omega)]

theorem abs_flip_mul (n : ℕ) (x : ℝ) : |(-1) ^ n * x| = |x| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-! ## The parities of the features -/

theorem kblocks_mem : ∀ (bl : List (List Blk)), kblocksOk bl = true → ∀ blks ∈ bl, blkParOk blks = true
  | [], _, blks, hm => by simp at hm
  | a :: l, h, blks, hm => by
    have h' : (blkParOk a && kblocksOk l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h'.1
    · exact kblocks_mem l h'.2 blks hm

theorem blkPar_mem : ∀ (blks : List Blk), blkParOk blks = true → ∀ blk ∈ blks, exAll blk.a blk.b blk.odd blk.ex 0 = true
  | [], _, blk, hm => by simp at hm
  | a :: l, h, blk, hm => by
    have h' : (exAll a.a a.b a.odd a.ex 0 && blkParOk l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h'.1
    · exact blkPar_mem l h'.2 blk hm

theorem exAll_nth (a b odd : ℕ) : ∀ (ex : List (List ℕ)) (k : ℕ), exAll a b odd ex k = true →
    ∀ c, exOk (k + c) a b odd (nthL ex c) = true
  | [], _, _, _ => rfl
  | e :: ex, k, h, 0 => by
    have h' : (exOk k a b odd e && exAll a b odd ex (Nat.succ k)) = true := h
    rw [Bool.and_eq_true] at h'
    exact h'.1
  | e :: ex, k, h, c + 1 => by
    have h' : (exOk k a b odd e && exAll a b odd ex (Nat.succ k)) = true := h
    rw [Bool.and_eq_true] at h'
    have ih := exAll_nth a b odd ex (Nat.succ k) h'.2 c
    rw [show k + (c + 1) = Nat.succ k + c by omega]
    exact ih

/-- The features of every class of every block of the kernel have the parities of the block. -/
theorem kblocks_ex (hkb : kblocksOk P.kblocks = true) {blks : List Blk} (hb : blks ∈ P.kblocks) {blk : Blk}
    (hblk : blk ∈ blks) (c : ℕ) : exOk c blk.a blk.b blk.odd (nthL blk.ex c) = true := by
  have h := exAll_nth blk.a blk.b blk.odd blk.ex 0 (blkPar_mem blks (kblocks_mem _ hkb blks hb) blk hblk) c
  rw [Nat.zero_add] at h
  exact h

theorem exOk_mem {cls a b odd : ℕ} : ∀ (l : List ℕ), exOk cls a b odd l = true → ∀ f ∈ l,
    f < 256 ∧ (cls = 0 → Nat.land (Nat.shiftRight f 4) 1 = b ∧ odd = 0)
      ∧ (cls = 1 → Nat.land (Nat.shiftRight f 4) 1 = a ∧ odd = 0)
      ∧ (2 ≤ cls → Nat.land f 1 = a ∧ Nat.land (Nat.shiftRight f 4) 1 = b)
  | [], _, f, hf => by simp at hf
  | e :: l, h, f, hf => by
    have h' : (Nat.blt e 256
      && cond (Nat.beq cls 0) (Nat.beq (Nat.land (Nat.shiftRight e 4) 1) b && Nat.beq odd 0)
        (cond (Nat.beq cls 1) (Nat.beq (Nat.land (Nat.shiftRight e 4) 1) a && Nat.beq odd 0)
          (Nat.beq (Nat.land e 1) a && Nat.beq (Nat.land (Nat.shiftRight e 4) 1) b)) && exOk cls a b odd l) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    rcases List.mem_cons.1 hf with rfl | hf
    · refine ⟨lt_of_blt h1, fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
      · rw [hc] at h2
        have h2' : (Nat.beq (Nat.land (Nat.shiftRight f 4) 1) b && Nat.beq odd 0) = true := h2
        rw [Bool.and_eq_true] at h2'
        exact ⟨Nat.eq_of_beq_eq_true h2'.1, Nat.eq_of_beq_eq_true h2'.2⟩
      · rw [hc] at h2
        have h2' : (Nat.beq (Nat.land (Nat.shiftRight f 4) 1) a && Nat.beq odd 0) = true := h2
        rw [Bool.and_eq_true] at h2'
        exact ⟨Nat.eq_of_beq_eq_true h2'.1, Nat.eq_of_beq_eq_true h2'.2⟩
      · rw [beq_false_of_ne (by omega : cls ≠ 0), beq_false_of_ne (by omega : cls ≠ 1)] at h2
        have h2' : (Nat.beq (Nat.land f 1) a && Nat.beq (Nat.land (Nat.shiftRight f 4) 1) b) = true := h2
        rw [Bool.and_eq_true] at h2'
        exact ⟨Nat.eq_of_beq_eq_true h2'.1, Nat.eq_of_beq_eq_true h2'.2⟩
    · exact exOk_mem l h3 f hf

theorem land1_lt (x : ℕ) : Nat.land x 1 < 2 := by
  show x &&& 1 < 2
  rw [Nat.and_one_is_mod]
  omega

/-- What the features of a class say about a block, if there are any. -/
def BlkC (blk : Blk) (c : ℕ) : Prop :=
  (c = 0 → blk.b < 2 ∧ blk.odd = 0) ∧ (c = 1 → blk.a < 2 ∧ blk.odd = 0) ∧ (2 ≤ c → blk.a < 2 ∧ blk.b < 2)

theorem blkC_of {blk : Blk} {c : ℕ} (hex : exOk c blk.a blk.b blk.odd (nthL blk.ex c) = true)
    (hne : nthL blk.ex c ≠ []) : BlkC blk c := by
  obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨_, h0, h1, h2⟩ := exOk_mem _ hex f hf
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · obtain ⟨hb, ho⟩ := h0 hc
    exact ⟨by rw [← hb]; exact land1_lt _, ho⟩
  · obtain ⟨ha, ho⟩ := h1 hc
    exact ⟨by rw [← ha]; exact land1_lt _, ho⟩
  · obtain ⟨ha, hb⟩ := h2 hc
    exact ⟨by rw [← ha]; exact land1_lt _, by rw [← hb]; exact land1_lt _⟩

/-- The sign by which the columns of a block change when the class coordinates of a point change their signs. -/
noncomputable def chiF (blk : Blk) (c tp tq : ℕ) : ℝ :=
  (-1) ^ (if c = 0 then tq * blk.b else if c = 1 then tq * blk.a else tp * blk.a + tq * blk.b)

theorem neg_pow_congr {m n : ℕ} (h : m % 2 = n % 2) : (-1 : ℝ) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem land15_1 : ∀ f, f < 256 → Nat.land (Nat.land f 15) 1 = Nat.land f 1 := by decide +kernel

theorem mod_of_land {x a : ℕ} (h : Nat.land x 1 = a) : x % 2 = a % 2 := by
  have h' : x &&& 1 = a := h
  rw [Nat.and_one_is_mod] at h'
  rw [← h', Nat.mod_mod]

theorem featL_flip {blk : Blk} {c : ℕ} (hex : exOk c blk.a blk.b blk.odd (nthL blk.ex c) = true) {tp tq : ℕ}
    (htp : c < 2 → tp = 0) (a b : ℝ) :
    featL (nthL blk.ex c) ((-1) ^ tp * a) ((-1) ^ tq * b)
      = (featL (nthL blk.ex c) a b).map (fun m => chiF blk c tp tq * m) := by
  unfold featL
  rw [List.map_map]
  refine List.map_congr_left fun f hf => ?_
  obtain ⟨hlt, h0, h1, h2⟩ := exOk_mem _ hex f hf
  show mono2 f ((-1) ^ tp * a) ((-1) ^ tq * b) = chiF blk c tp tq * mono2 f a b
  unfold mono2 chiF
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  have key : (-1 : ℝ) ^ (tp * Nat.land f 15) * (-1) ^ (tq * Nat.shiftRight f 4)
      = (-1) ^ (if c = 0 then tq * blk.b else if c = 1 then tq * blk.a else tp * blk.a + tq * blk.b) := by
    rw [← pow_add]
    apply neg_pow_congr
    split_ifs with hc0 hc1
    · rw [htp (by omega), Nat.zero_mul, Nat.zero_add]
      exact Nat.ModEq.mul_left tq (mod_of_land (h0 hc0).1)
    · rw [htp (by omega), Nat.zero_mul, Nat.zero_add]
      exact Nat.ModEq.mul_left tq (mod_of_land (h1 hc1).1)
    · obtain ⟨ha, hb⟩ := h2 (by omega)
      have ha' : Nat.land (Nat.land f 15) 1 = blk.a := by rw [land15_1 f hlt, ha]
      exact (Nat.ModEq.mul_left tp (mod_of_land ha')).add (Nat.ModEq.mul_left tq (mod_of_land hb))
  rw [← key]
  ring

theorem dotR_map_mul (w : ℕ) (χ : ℝ) : ∀ (ms : List ℝ) (N : ℕ), dotR w (ms.map (fun m => χ * m)) N = χ * dotR w ms N
  | [], _ => by
    show (0 : ℝ) = χ * 0
    ring
  | m :: l, N => by
    show ((Nat.land N (mask w) : ℕ) : ℝ) * (χ * m) + dotR w (l.map (fun m => χ * m)) (Nat.shiftRight N w)
      = χ * (((Nat.land N (mask w) : ℕ) : ℝ) * m + dotR w l (Nat.shiftRight N w))
    rw [dotR_map_mul w χ l]
    ring

theorem sum_map_mul (χ : ℝ) : ∀ ms : List ℝ, (ms.map (fun m => χ * m)).sum = χ * ms.sum
  | [] => by simp
  | m :: l => by
    rw [List.map_cons, List.sum_cons, List.sum_cons, sum_map_mul χ l]
    ring

theorem psi_map_mul (blk : Blk) (c : ℕ) (χ : ℝ) (ms : List ℝ) (col : ℕ) :
    psi blk c (ms.map (fun m => χ * m)) col = χ * psi blk c ms col := by
  unfold psi
  rw [dotR_map_mul, sum_map_mul]
  ring

theorem sum_mul_map {α : Type} (r : ℝ) (f : α → ℝ) : ∀ l : List α, r * (l.map f).sum = (l.map (fun a => r * f a)).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, ← sum_mul_map r f l]
    ring

/-! ## The covariance of the kernel -/

/-- **The blocks of the kernel at the end points of a record are those of the two labels.** The end point of
the label `i` has the variables `0`, `1` and the signs `tp1`, `tq1` of its class coordinates, the end point of
the label `j` the variables `ip2`, `iq2` and the signs `tp2`, `tq2`; `hsign` states that the signs of the two
end points cancel in every block in which both classes have features. -/
theorem inner_cov {c1 s1 c2 s2 tp1 tq1 tp2 tq2 ip2 iq2 : ℕ} (hkb : kblocksOk P.kblocks = true)
    (hc1 : nth P.dcls i = c1) (hc2 : nth P.dcls j = c2)
    (hat1 : At y 0 1 ((-1) ^ tp1 * cp P C i) ((-1) ^ tq1 * cq P C i))
    (hat2 : At y ip2 iq2 ((-1) ^ tp2 * cp P C j) ((-1) ^ tq2 * cq P C j))
    (ht1 : c1 < 2 → tp1 = 0) (ht2 : c2 < 2 → tp2 = 0)
    (hsign : ∀ blk : Blk, BlkC blk c1 → BlkC blk c2 →
      sgnR (sgnOf c1 s1 blk) * sgnR (sgnOf c2 s2 blk) * (chiF blk c1 tp1 tq1 * chiF blk c2 tp2 tq2)
        = sgnR (sgnOf c1 (nth P.dsg i) blk) * sgnR (sgnOf c2 (nth P.dsg j) blk))
    (W : ℕ) (L : Lay) :
    ∀ blks ∈ P.kblocks, innerK (realOps W L y) c1 s1 0 1 c2 s2 ip2 iq2 blks 0 = Kb P C i j blks := by
  intro blks hblks
  rw [innerK_real, zero_add]
  unfold Kb
  congr 1
  refine List.map_congr_left fun blk hblk => ?_
  have hex1 := kblocks_ex hkb hblks hblk c1
  have hex2 := kblocks_ex hkb hblks hblk c2
  rw [blkBil_real, monoListAt_real hat1 _ (fun c hc => (exOk_mem _ hex1 c hc).1),
    monoListAt_real hat2 _ (fun c hc => (exOk_mem _ hex2 c hc).1), featL_flip hex1 ht1, featL_flip hex2 ht2,
    sgnR_mul (sgnOf_le _ _ _) (sgnOf_le _ _ _), sum_mul_map]
  refine congrArg List.sum (List.map_congr_left fun col _ => ?_)
  rw [psi_map_mul, psi_map_mul]
  unfold Psi
  rw [hc1, hc2]
  by_cases h1 : nthL blk.ex c1 = []
  · rw [h1]
    simp [featL, psi_nil]
  by_cases h2 : nthL blk.ex c2 = []
  · rw [h2]
    simp [featL, psi_nil]
  have hs := hsign blk (blkC_of hex1 h1) (blkC_of hex2 h2)
  linear_combination (psi blk c1 (featL (nthL blk.ex c1) (cp P C i) (cq P C i)) col
    * psi blk c2 (featL (nthL blk.ex c2) (cp P C j) (cq P C j)) col) * hs

/-! ## The signs of the blocks -/

theorem sgnR0 : sgnR 0 = 0 := by
  show ((0 : ℤ) : ℝ) = 0
  simp

theorem sgnR1 : sgnR 1 = 1 := by
  show ((1 : ℤ) : ℝ) = 1
  simp

theorem sgnR2 : sgnR 2 = -1 := by
  show ((-1 : ℤ) : ℝ) = -1
  simp

theorem sgnR_sgnOf0 (sg : ℕ) (blk : Blk) : sgnR (sgnOf 0 sg blk) = if sg = 1 ∧ blk.a = 1 then -1 else 1 := by
  have e : sgnOf 0 sg blk = cond (Nat.beq sg 1 && Nat.beq blk.a 1) 2 1 := rfl
  rw [e]
  by_cases h1 : sg = 1
  · by_cases h2 : blk.a = 1
    · rw [h1, h2, if_pos ⟨rfl, rfl⟩]
      exact sgnR2
    · rw [beq_false_of_ne h2, if_neg (fun h => h2 h.2), Bool.and_false]
      exact sgnR1
  · rw [beq_false_of_ne h1, if_neg (fun h => h1 h.1), Bool.false_and]
    exact sgnR1

theorem sgnR_sgnOf1 (sg : ℕ) (blk : Blk) : sgnR (sgnOf 1 sg blk) = if sg = 1 ∧ blk.b = 1 then -1 else 1 := by
  have e : sgnOf 1 sg blk = cond (Nat.beq sg 1 && Nat.beq blk.b 1) 2 1 := rfl
  rw [e]
  by_cases h1 : sg = 1
  · by_cases h2 : blk.b = 1
    · rw [h1, h2, if_pos ⟨rfl, rfl⟩]
      exact sgnR2
    · rw [beq_false_of_ne h2, if_neg (fun h => h2 h.2), Bool.and_false]
      exact sgnR1
  · rw [beq_false_of_ne h1, if_neg (fun h => h1 h.1), Bool.false_and]
    exact sgnR1

theorem sgnOf_ring {c : ℕ} (hc : 2 ≤ c) (sg : ℕ) (blk : Blk) :
    sgnOf c sg blk = cond (Nat.beq blk.odd 1) (cond (Nat.beq sg 0) 0 (cond (Nat.beq sg 1) 1 2)) 1 := by
  unfold sgnOf
  rw [beq_false_of_ne (by omega : c ≠ 0), beq_false_of_ne (by omega : c ≠ 1)]
  rfl

theorem sgnR_ring_even {c : ℕ} (hc : 2 ≤ c) (sg : ℕ) {blk : Blk} (ho : blk.odd ≠ 1) : sgnR (sgnOf c sg blk) = 1 := by
  rw [sgnOf_ring hc, beq_false_of_ne ho]
  exact sgnR1

theorem sgnR_ring_odd {c : ℕ} (hc : 2 ≤ c) (sg : ℕ) {blk : Blk} (ho : blk.odd = 1) :
    sgnR (sgnOf c sg blk) = if sg = 0 then 0 else if sg = 1 then 1 else -1 := by
  rw [sgnOf_ring hc, ho]
  by_cases h0 : sg = 0
  · rw [h0, if_pos rfl]
    exact sgnR0
  · by_cases h1 : sg = 1
    · rw [h1, if_neg (by omega), if_pos rfl]
      exact sgnR1
    · rw [if_neg h0, if_neg h1, beq_false_of_ne h0, beq_false_of_ne h1]
      exact sgnR2

/-! ## The class coordinates lie in the cube -/

theorem abs_le_one_of_sq {x : ℝ} (h : x ^ 2 ≤ 1) : |x| ≤ 1 := by
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]

theorem pcOk_real {c : PairConst} (h : pcOk c = true) :
    (c.aPn : ℝ) ≤ c.aPd ∧ (c.aQ2n : ℝ) ≤ c.aQ2d ∧ (1 : ℝ) ≤ c.aPd ∧ (1 : ℝ) ≤ c.aQ2d := by
  unfold pcOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩, _⟩ := h
  exact ⟨by exact_mod_cast Nat.le_of_ble_eq_true h1, by exact_mod_cast Nat.le_of_ble_eq_true h2,
    by exact_mod_cast Nat.le_of_ble_eq_true h3, by exact_mod_cast Nat.le_of_ble_eq_true h4⟩

theorem constsOk_real (h : constsOk P = true) :
    pcOk P.cA = true ∧ pcOk P.cB = true ∧ (P.eR2n : ℝ) ≤ P.eR2d ∧ (1 : ℝ) ≤ P.eR2d := by
  unfold constsOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩ := h
  exact ⟨h1, h2, by exact_mod_cast Nat.le_of_ble_eq_true h3, by exact_mod_cast Nat.le_of_ble_eq_true h4⟩

theorem pairPt_cube {c : PairConst} (hc : pcOk c = true) {mP mQ : ℕ} {M N Rv : ℝ} (hpt : PairPt c mP mQ M N Rv)
    (hM : M ≤ 1) : |2 ^ mP * (1 - M)| ≤ 1 ∧ |2 ^ mQ * N| ≤ 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := pcOk_real hc
  constructor
  · rw [abs_le]
    have h0 : (0 : ℝ) ≤ 2 ^ mP * (1 - M) := mul_nonneg (by positivity) (by linarith)
    refine ⟨by linarith, ?_⟩
    have := hpt.major
    nlinarith
  · apply abs_le_one_of_sq
    have := hpt.minor
    nlinarith [sq_nonneg (2 ^ mQ * N)]

theorem le_one_of_unit {a b c d : ℝ} (h : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1) : a ≤ 1 ∧ -1 ≤ a := by
  constructor <;> nlinarith [sq_nonneg (a - 1), sq_nonneg (a + 1), sq_nonneg b, sq_nonneg c, sq_nonneg d]

/-- **The class coordinates of a label lie in `[-1, 1]`.** -/
theorem cp_abs (lab : LabOk P heads) (hin : InPiece P heads C) {l : ℕ} (hl : l < 9) :
    |cp P C l| ≤ 1 ∧ |cq P C l| ≤ 1 := by
  obtain ⟨hA, hB, hR1, hR2⟩ := constsOk_real lab.consts
  have hu := hin.unit l hl
  by_cases h2 : l < 2
  · have hM : eps l * C.u l ≤ 1 := by
      have : (eps l * C.u l) ^ 2 + C.v l ^ 2 + C.ξ l ^ 2 + C.η l ^ 2 = 1 := by
        rw [mul_pow, eps_sq, one_mul]
        exact hu
      exact (le_one_of_unit this).1
    have := pairPt_cube hA (hin.pairA l h2) hM
    unfold cp cq
    rw [if_pos h2, if_pos h2]
    exact this
  · by_cases h4 : l < 4
    · have hM : eps l * C.v l ≤ 1 := by
        have : (eps l * C.v l) ^ 2 + C.u l ^ 2 + C.ξ l ^ 2 + C.η l ^ 2 = 1 := by
          rw [mul_pow, eps_sq, one_mul]
          linarith
        exact (le_one_of_unit this).1
      have := pairPt_cube hB (hin.pairB l (by omega) h4) hM
      unfold cp cq
      rw [if_neg h2, if_pos h4, if_neg h2, if_pos h4]
      exact this
    · obtain ⟨r1, r2, _, _⟩ := hin.ring l (by omega) hl
      unfold cp cq
      rw [if_neg h2, if_neg h4, if_neg h2, if_neg h4]
      exact ⟨abs_le_one_of_sq (by nlinarith [sq_nonneg (C.u l)]), abs_le_one_of_sq (by nlinarith [sq_nonneg (C.v l)])⟩

/-! ## Intervals -/

/-- An interval `[lo, hi]` inside `[(c0 - 2 ^ jd) / 2 ^ mT, (c0 + 2 ^ jd) / 2 ^ mT]`: the centred variable lies in
`[-1, 1]`. -/
theorem interval_real {c0p c0n jd mT : ℕ} {h : RecH} (hi : intervalOk c0p c0n jd mT h = true) (hlod : 1 ≤ h.lod)
    (hhid : 1 ≤ h.hid) {t : ℝ} (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * t) (hhi : (h.hid : ℝ) * t ≤ (h.hip : ℝ) - h.hin) :
    |(2 ^ mT * t - ((c0p : ℝ) - c0n)) / 2 ^ jd| ≤ 1 := by
  unfold intervalOk at hi
  rw [Bool.and_eq_true] at hi
  have h1 : h.lod * c0p + h.lon * 2 ^ mT ≤ h.lod * (c0n + 2 ^ jd) + h.lop * 2 ^ mT := by
    have := Nat.le_of_ble_eq_true hi.1
    rw [show Nat.shiftLeft 1 mT = 2 ^ mT from Nat.one_shiftLeft mT, show Nat.shiftLeft 1 jd = 2 ^ jd from Nat.one_shiftLeft jd]
      at this
    exact this
  have h2 : h.hip * 2 ^ mT + h.hid * c0n ≤ h.hid * (c0p + 2 ^ jd) + h.hin * 2 ^ mT := by
    have := Nat.le_of_ble_eq_true hi.2
    rw [show Nat.shiftLeft 1 mT = 2 ^ mT from Nat.one_shiftLeft mT, show Nat.shiftLeft 1 jd = 2 ^ jd from Nat.one_shiftLeft jd]
      at this
    exact this
  have h1' : (h.lod : ℝ) * c0p + h.lon * 2 ^ mT ≤ h.lod * (c0n + 2 ^ jd) + h.lop * 2 ^ mT := by exact_mod_cast h1
  have h2' : (h.hip : ℝ) * 2 ^ mT + h.hid * c0n ≤ h.hid * (c0p + 2 ^ jd) + h.hin * 2 ^ mT := by exact_mod_cast h2
  have hl : (1 : ℝ) ≤ h.lod := by exact_mod_cast hlod
  have hh : (1 : ℝ) ≤ h.hid := by exact_mod_cast hhid
  have hT : (0 : ℝ) ≤ 2 ^ mT := by positivity
  have hJ : (0 : ℝ) < 2 ^ jd := by positivity
  rw [abs_le, le_div_iff₀ hJ, div_le_iff₀ hJ]
  constructor
  · have a1 := mul_le_mul_of_nonneg_right hlo hT
    have : (0 : ℝ) ≤ h.lod * (2 ^ mT * t - ((c0p : ℝ) - c0n) + 2 ^ jd) := by nlinarith
    have := nonneg_of_mul_nonneg_right this (by linarith)
    linarith
  · have a1 := mul_le_mul_of_nonneg_right hhi hT
    have : (0 : ℝ) ≤ h.hid * (2 ^ jd - (2 ^ mT * t - ((c0p : ℝ) - c0n))) := by nlinarith
    have := nonneg_of_mul_nonneg_right this (by linarith)
    linarith

/-- The content of the check `rangesOk`. -/
theorem rangesOk_real {h : RecH} (hr : rangesOk h = true) :
    h.hip < h.hid + h.hin ∧ 1 ≤ h.lod ∧ 1 ≤ h.hid
      ∧ (h.kind = 5 → intervalOk h.c0p h.c0n h.jd h.mTr h = true)
      ∧ (2 ≤ h.kind → h.kind ≤ 4 → (h.aS2n : ℝ) ≤ h.aS2d ∧ (1 : ℝ) ≤ h.aS2d)
      ∧ (h.hform = 1 → intervalOk (Nat.shiftLeft h.hc0p h.hj) (Nat.shiftLeft h.hc0n h.hj) h.hm (Nat.add h.hm h.hj) h = true) := by
  unfold rangesOk at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, _⟩, h5⟩, h6⟩, h7⟩ := hr
  refine ⟨lt_of_blt h1, Nat.le_of_ble_eq_true h2, Nat.le_of_ble_eq_true h3, fun hk => ?_, fun hk2 hk4 => ?_, fun hf => ?_⟩
  · rw [hk] at h5
    exact h5
  · rw [Nat.ble_eq_true_of_le hk2, Nat.ble_eq_true_of_le hk4] at h6
    have h6' : (Nat.ble h.aS2n h.aS2d && Nat.ble 1 h.aS2d) = true := h6
    rw [Bool.and_eq_true] at h6'
    exact ⟨by exact_mod_cast Nat.le_of_ble_eq_true h6'.1, by exact_mod_cast Nat.le_of_ble_eq_true h6'.2⟩
  · rw [hf] at h7
    exact h7

/-! ## The facts on the minorant of a pair -/

/-- The facts on the minorant of the pair `i < j` at the data `y`, with the point `(m0, m1)` of the minorant. -/
structure MinoFacts (P : Par) (C : Conf) (i j : ℕ) (h : RecH) (y : Fin 5 → ℝ) (m0 m1 : ℝ) : Prop where
  hm0 : ∀ (W : ℕ) (L : Lay), Nat.beq h.hform 0 = true →
    recHm (realOps W L y) P h (2 ^ recMT P h * C.t i j) (recMT P h) = poly2 P.wP h.hex h.hp h.hn m0 m1
  hm1 : ∀ (W : ℕ) (L : Lay), Nat.beq h.hform 0 = false →
    2 ^ (h.hm + recMT P h) * recHm (realOps W L y) P h (2 ^ recMT P h * C.t i j) (recMT P h)
      = 2 ^ ((h.hm + recMT P h) * len h.hex) * poly2 P.wP h.hex h.hp h.hn m0 m1
  mcube : |m0| ≤ 1 ∧ |m1| ≤ 1
  mT : ∀ (W : ℕ) (L : Lay), minoT (realOps W L ![m0, m1, 0, 0, 0]) h = 2 ^ minoMM h * C.t i j
  mlocs : ∀ (W : ℕ) (L : Lay),
    ∀ g ∈ minoLocs (realOps W L ![m0, m1, 0, 0, 0]) P h (2 ^ minoMM h * C.t i j) (minoMM h), 0 ≤ g
  mcodes : ∀ c ∈ h.hex, c < 256

theorem iotaOk_lt : ∀ (l : List ℕ) (k : ℕ), iotaOk l k = true → ∀ c ∈ l, c < 16
  | [], _, _, c, hc => by simp at hc
  | a :: l, k, h, c, hc => by
    have h' : (Nat.beq a k && Nat.blt a 16 && iotaOk l (Nat.succ k)) = true := h
    simp only [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact lt_of_blt h'.1.2
    · exact iotaOk_lt l _ h'.2 c hc

/-- The content of the check `formOk`. -/
theorem formOk_real {h : RecH} (hf : formOk h = true) :
    (∀ c ∈ h.p1ex, c < 256) ∧ (∀ c ∈ h.p2ex, c < 256)
      ∧ (h.hform = 0 → (∀ c ∈ h.hex, c < 256)
        ∧ ((h.kind = 3 ∧ h.hia = 2 ∧ h.hib = 4) ∨ (h.kind = 4 ∧ h.hia = 3 ∧ h.hib = 4)
          ∨ (h.kind = 5 ∧ h.hia = 4 ∧ h.hib = 0)))
      ∧ (h.hform ≠ 0 → h.hform = 1 ∧ iotaOk h.hex 0 = true ∧ h.kind ≠ 3 ∧ h.kind ≠ 4) := by
  unfold formOk at hf
  simp only [Bool.and_eq_true] at hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨codesOk_lt _ h1, codesOk_lt _ h2, fun h0 => ?_, fun h0 => ?_⟩
  · rw [h0] at h3
    have h3' : (codesOk h.hex
        && ((Nat.beq h.kind 3 && Nat.beq h.hia 2 && Nat.beq h.hib 4)
          || (Nat.beq h.kind 4 && Nat.beq h.hia 3 && Nat.beq h.hib 4)
          || (Nat.beq h.kind 5 && Nat.beq h.hia 4 && Nat.beq h.hib 0))) = true := h3
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h3'
    refine ⟨codesOk_lt _ h3'.1, ?_⟩
    rcases h3'.2 with (⟨⟨a, b⟩, c⟩ | ⟨⟨a, b⟩, c⟩) | ⟨⟨a, b⟩, c⟩
    · exact Or.inl ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩
    · exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩)
    · exact Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c⟩)
  · rw [beq_false_of_ne h0] at h3
    have h3' : (Nat.beq h.hform 1 && iotaOk h.hex 0 && !(Nat.beq h.kind 3) && !(Nat.beq h.kind 4)) = true := h3
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h3'
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h3'
    refine ⟨Nat.eq_of_beq_eq_true a, b, fun hk => ?_, fun hk => ?_⟩
    · rw [hk] at c
      exact absurd c (by decide)
    · rw [hk] at d
      exact absurd d (by decide)

/-- The weights of the identity of a minorant in one variable are nonnegative on the interval. -/
theorem minoLocs_uni {h : RecH} (hb : minoBiv h = false) (mM : ℕ) {t : ℝ} (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * t)
    (hhi : (h.hid : ℝ) * t ≤ (h.hip : ℝ) - h.hin) (W : ℕ) (L : Lay) (y' : Fin 5 → ℝ) :
    ∀ g ∈ minoLocs (realOps W L y') P h (2 ^ mM * t) mM, 0 ≤ g := by
  intro g hg
  unfold minoLocs at hg
  rw [hb] at hg
  have hg' : g ∈ [(h.lod : ℝ) * (2 ^ mM * t) + ((Nat.mul h.lon (Nat.shiftLeft 1 mM) : ℕ) : ℝ)
        - ((Nat.mul h.lop (Nat.shiftLeft 1 mM) : ℕ) : ℝ),
      ((Nat.mul h.hip (Nat.shiftLeft 1 mM) : ℕ) : ℝ)
        - ((h.hid : ℝ) * (2 ^ mM * t) + ((Nat.mul h.hin (Nat.shiftLeft 1 mM) : ℕ) : ℝ))] := hg
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg'
  have h2 : (0 : ℝ) ≤ 2 ^ mM := by positivity
  rcases hg' with rfl | rfl
  · rw [cast_mul_shl, cast_mul_shl]
    have e : (h.lod : ℝ) * (2 ^ mM * t) + (h.lon : ℝ) * 2 ^ mM - (h.lop : ℝ) * 2 ^ mM
        = 2 ^ mM * ((h.lod : ℝ) * t - ((h.lop : ℝ) - h.lon)) := by ring
    rw [e]
    exact mul_nonneg h2 (by linarith)
  · rw [cast_mul_shl, cast_mul_shl]
    have e : (h.hip : ℝ) * 2 ^ mM - ((h.hid : ℝ) * (2 ^ mM * t) + (h.hin : ℝ) * 2 ^ mM)
        = 2 ^ mM * ((h.hip : ℝ) - h.hin - h.hid * t) := by ring
    rw [e]
    exact mul_nonneg h2 (by linarith)

theorem vec0 (m0 m1 : ℝ) : var (realOps W L ![m0, m1, 0, 0, 0]) 0 = m0 := by
  rw [var0]
  rfl

theorem vec1 (m0 m1 : ℝ) : var (realOps W L ![m0, m1, 0, 0, 0]) 1 = m1 := by
  rw [var1]
  rfl

/-- **A minorant in the centred inner product** (the Horner form in the record). -/
theorem mino_h1 {h : RecH} (hf : formOk h = true) (hr : rangesOk h = true) (h1 : h.hform ≠ 0)
    (hlo : (h.lop : ℝ) - h.lon ≤ h.lod * C.t i j) (hhi : (h.hid : ℝ) * C.t i j ≤ (h.hip : ℝ) - h.hin)
    (y : Fin 5 → ℝ) :
    MinoFacts P C i j h y (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) 0 := by
  obtain ⟨_, _, _, hF⟩ := formOk_real hf
  obtain ⟨hf1, hiota, hk3, hk4⟩ := hF h1
  obtain ⟨_, hlod, hhid, _, _, hI⟩ := rangesOk_real hr
  have hb : minoBiv h = false := by
    unfold minoBiv
    rw [beq_false_of_ne hk3, beq_false_of_ne hk4]
    rfl
  have hM : minoMM h = h.hm + h.hj := by
    unfold minoMM
    rw [hb, hf1]
    rfl
  have hX : (2 : ℝ) ^ h.hm ≠ 0 := by positivity
  refine
    { hm0 := fun W L hb0 => absurd (Nat.eq_of_beq_eq_true hb0) h1
      hm1 := fun W L _ => ?_
      mcube := ⟨?_, by simp⟩
      mT := fun W L => ?_
      mlocs := fun W L => ?_
      mcodes := fun c hc => by
        have := iotaOk_lt _ _ hiota c hc
        omega }
  · -- the Horner form
    have hthat : recThat (realOps W L y) h (2 ^ recMT P h * C.t i j) (recMT P h)
        = 2 ^ (h.hm + recMT P h) * (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) := by
      show ((Nat.shiftLeft 1 h.hj : ℕ) : ℝ) * (((Nat.shiftLeft 1 h.hm : ℕ) : ℝ) * (2 ^ recMT P h * C.t i j)
          + ((Nat.shiftLeft h.hc0n (recMT P h) : ℕ) : ℝ) - ((Nat.shiftLeft h.hc0p (recMT P h) : ℕ) : ℝ)) = _
      rw [cast_shl1, cast_shl1, cast_shl, cast_shl, pow_add]
      field_simp
      ring
    have hrec : recHm (realOps W L y) P h (2 ^ recMT P h * C.t i j) (recMT P h)
        = hornerGo (realOps W L y) P.wP (mask P.wP) h.hp h.hn
          (recThat (realOps W L y) h (2 ^ recMT P h * C.t i j) (recMT P h)) (h.hm + recMT P h) (len h.hex) 0
          ((0 : ℕ) : ℝ) := by
      unfold recHm
      rw [beq_false_of_ne h1]
      rfl
    have hpoly : poly2 P.wP h.hex h.hp h.hn (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) 0
        = hsum P.wP h.hp h.hn (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) (len h.hex) := by
      have := poly2_iota P.wP h.hp h.hn (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) 0 h.hex 0 hiota
      rw [Nat.zero_add, ← len_eq] at this
      have e0 : hsum P.wP h.hp h.hn (2 ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)) 0 = 0 := rfl
      rw [e0, sub_zero] at this
      exact this
    rw [hrec, hthat, hornerGo_real, hpoly]
    simp
  · -- the centred inner product lies in `[-1, 1]`
    have hI' := interval_real (hI hf1) hlod hhid hlo hhi
    have e : (2 : ℝ) ^ h.hj * (C.t i j - ((h.hc0p : ℝ) - h.hc0n) / 2 ^ h.hm)
        = (2 ^ (Nat.add h.hm h.hj) * C.t i j
          - (((Nat.shiftLeft h.hc0p h.hj : ℕ) : ℝ) - ((Nat.shiftLeft h.hc0n h.hj : ℕ) : ℝ))) / 2 ^ h.hm := by
      rw [cast_shl, cast_shl]
      show _ = (2 ^ (h.hm + h.hj) * C.t i j - _) / _
      rw [pow_add]
      field_simp
    rw [e]
    exact hI'
  · unfold minoT
    rw [hb, hf1, hM]
    show ((Nat.shiftLeft h.hc0p h.hj : ℕ) : ℝ)
      + ((Nat.shiftLeft 1 h.hm : ℕ) : ℝ) * var (realOps W L ![_, _, 0, 0, 0]) 0 - ((Nat.shiftLeft h.hc0n h.hj : ℕ) : ℝ) = _
    rw [vec0, cast_shl1, cast_shl, cast_shl, pow_add]
    field_simp
    ring
  · exact minoLocs_uni hb _ hlo hhi W L _

end CAP.VR
