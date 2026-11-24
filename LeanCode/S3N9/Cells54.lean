module

public import S3N9.Cells

/-!
# The theorem for nine points: a separated chain outside the cell L3-k2 lies in a claim of the 54 cells

* `mval`: the inner product of the pair `c` of a labelled configuration;
* `inPC_of_chain`: `pairClaim_of_chain` for the data of a pair claim, with the numbers `mval y c`.
-/

@[expose] public section

namespace S3N9

open Finset

/-- The inner product of the pair `c < 4` of a labelled configuration: of the positions `2 c` and `2 c + 1`. -/
noncomputable def mval (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) (c : ℕ) : ℝ :=
  if h : 2 * c + 1 < 9 then inner ℝ (y ⟨2 * c, by omega⟩) (y ⟨2 * c + 1, h⟩) else 0

theorem mval_eq {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} {c : ℕ} {a b : Fin 9} (ha : a.val = 2 * c)
    (hb : b.val = 2 * c + 1) : inner ℝ (y a) (y b) = mval y c := by
  have h : 2 * c + 1 < 9 := by
    have := b.isLt
    omega
  unfold mval
  rw [dif_pos h]
  have ea : a = ⟨2 * c, by omega⟩ := Fin.ext ha
  have eb : b = ⟨2 * c + 1, h⟩ := Fin.ext hb
  rw [ea, eb]

/-- The inner products of the pairs of a chain increase. -/
theorem mval_mono {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hc : IsChain y 4) {c d : ℕ} (hcd : c ≤ d) (hd : d < 4) :
    mval y c ≤ mval y d := by
  obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * c := ⟨⟨2 * c, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * c + 1 := ⟨⟨2 * c + 1, by omega⟩, rfl⟩
  obtain ⟨m, hm⟩ : ∃ r : Fin 9, r.val = 2 * d := ⟨⟨2 * d, by omega⟩, rfl⟩
  obtain ⟨n, hn⟩ : ∃ r : Fin 9, r.val = 2 * d + 1 := ⟨⟨2 * d + 1, by omega⟩, rfl⟩
  rw [← mval_eq ha hb, ← mval_eq hm hn]
  exact hc c (by omega) a b ha hb m n (by omega) (by omega) (fun h => by
    have := congrArg Fin.val h
    omega)

/-- **A chain lies in a pair claim**, for the data of the claim: the first `k` pairs of the chain are near, the
next one is not, the inner products of the first pairs lie in the intervals of the claim, and the next inner
product is at least the bound of the last class. -/
theorem inPC_of_chain {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) {k : ℕ} (c : PC) (hkp : k ≤ c.I.length) (hp : c.I.length ≤ 4)
    (hnear : ∀ i < k, mval y i ≤ -(9 : ℝ) / 10) (hfar : k < 4 → -(9 : ℝ) / 10 < mval y k)
    (hI : ∀ i < c.I.length, ((c.I.getD i (0, 0)).1 : ℝ) / 2000 ≤ mval y i
      ∧ mval y i ≤ ((c.I.getD i (0, 0)).2 : ℝ) / 2000)
    (hℓ : c.I.length < 4 → (c.l : ℝ) / 2000 ≤ mval y c.I.length) : InPC c y :=
  pairClaim_of_chain hu hs hc hkp hp
    (fun i hi a b ha hb => by rw [mval_eq ha hb]; exact hnear i hi)
    (fun hk a b ha hb => by rw [mval_eq ha hb]; exact hfar hk)
    (fun i hi a b ha hb => by rw [mval_eq ha hb]; exact hI i hi)
    (fun hl a b ha hb => by rw [mval_eq ha hb]; exact hℓ hl)

/-- The inner product of two unit vectors is at least `-1`. -/
theorem neg_one_le_mval {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) {c : ℕ} (hc : c < 4) :
    -1 ≤ mval y c := by
  obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * c := ⟨⟨2 * c, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * c + 1 := ⟨⟨2 * c + 1, by omega⟩, rfl⟩
  rw [← mval_eq ha hb]
  have h := abs_real_inner_le_norm (y a) (y b)
  rw [hu, hu, mul_one] at h
  exact (abs_le.1 h).1

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)
  {k : ℕ} (hnear : ∀ i < k, mval y i ≤ -(9 : ℝ) / 10) (hfar : k < 4 → -(9 : ℝ) / 10 < mval y k)

include hu hs hc hnear hfar

theorem inPC1 (hk : k ≤ 1) {s0 : ℤ × ℤ} {l : ℤ}
    (h0 : (s0.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s0.2 : ℝ) / 2000) (hl : (l : ℝ) / 2000 ≤ mval y 1) :
    InPC ⟨[s0], l⟩ y :=
  inPC_of_chain hu hs hc ⟨[s0], l⟩ hk (by show 1 ≤ 4; norm_num) hnear hfar
    (fun i hi => by
      have hi' : i < 1 := hi
      interval_cases i
      exact h0)
    (fun _ => hl)

theorem inPC2 (hk : k ≤ 2) {s0 s1 : ℤ × ℤ} {l : ℤ}
    (h0 : (s0.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s0.2 : ℝ) / 2000)
    (h1 : (s1.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (s1.2 : ℝ) / 2000) (hl : (l : ℝ) / 2000 ≤ mval y 2) :
    InPC ⟨[s0, s1], l⟩ y :=
  inPC_of_chain hu hs hc ⟨[s0, s1], l⟩ hk (by show 2 ≤ 4; norm_num) hnear hfar
    (fun i hi => by
      have hi' : i < 2 := hi
      interval_cases i
      · exact h0
      · exact h1)
    (fun _ => hl)

theorem inPC3 (hk : k ≤ 3) {s0 s1 s2 : ℤ × ℤ} {l : ℤ}
    (h0 : (s0.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s0.2 : ℝ) / 2000)
    (h1 : (s1.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (s1.2 : ℝ) / 2000)
    (h2 : (s2.1 : ℝ) / 2000 ≤ mval y 2 ∧ mval y 2 ≤ (s2.2 : ℝ) / 2000) (hl : (l : ℝ) / 2000 ≤ mval y 3) :
    InPC ⟨[s0, s1, s2], l⟩ y :=
  inPC_of_chain hu hs hc ⟨[s0, s1, s2], l⟩ hk (by show 3 ≤ 4; norm_num) hnear hfar
    (fun i hi => by
      have hi' : i < 3 := hi
      interval_cases i
      · exact h0
      · exact h1
      · exact h2)
    (fun _ => hl)

theorem inPC4 (hk : k ≤ 4) {s0 s1 s2 s3 : ℤ × ℤ} {l : ℤ}
    (h0 : (s0.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s0.2 : ℝ) / 2000)
    (h1 : (s1.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (s1.2 : ℝ) / 2000)
    (h2 : (s2.1 : ℝ) / 2000 ≤ mval y 2 ∧ mval y 2 ≤ (s2.2 : ℝ) / 2000)
    (h3 : (s3.1 : ℝ) / 2000 ≤ mval y 3 ∧ mval y 3 ≤ (s3.2 : ℝ) / 2000) :
    InPC ⟨[s0, s1, s2, s3], l⟩ y :=
  inPC_of_chain hu hs hc ⟨[s0, s1, s2, s3], l⟩ hk (by show 4 ≤ 4; norm_num) hnear hfar
    (fun i hi => by
      have hi' : i < 4 := hi
      interval_cases i
      · exact h0
      · exact h1
      · exact h2
      · exact h3)
    (fun h => absurd h (by show ¬ 4 < 4; norm_num))

end

/-! ## The thresholds as real numbers -/

theorem th_eq : ((Cell.th : ℤ) : ℝ) / 2000 = -9 / 10 := by norm_num [Cell.th]
theorem b0_eq : ((Cell.b0 : ℤ) : ℝ) / 2000 = -7 / 8 := by norm_num [Cell.b0]
theorem k2_eq : ((Cell.k2 : ℤ) : ℝ) / 2000 = -43 / 50 := by norm_num [Cell.k2]
theorem kr_eq : ((Cell.kr : ℤ) : ℝ) / 2000 = -4 / 5 := by norm_num [Cell.kr]
theorem sg_eq : ((Cell.sg : ℤ) : ℝ) / 2000 = -17 / 20 := by norm_num [Cell.sg]
theorem a1_eq : ((Cell.a1 : ℤ) : ℝ) / 2000 = -99 / 100 := by norm_num [Cell.a1]
theorem m1_eq : ((Cell.m1 : ℤ) : ℝ) / 2000 = -1 := by norm_num [Cell.m1]

/-- A number in the interval with the ends `a / 2000`, `b / 2000`. -/
theorem ivl {m : ℝ} {a b : ℤ} (ha : (a : ℝ) / 2000 ≤ m) (hb : m ≤ (b : ℝ) / 2000) :
    (((a, b) : ℤ × ℤ).1 : ℝ) / 2000 ≤ m ∧ m ≤ (((a, b) : ℤ × ℤ).2 : ℝ) / 2000 := ⟨ha, hb⟩

/-! ## The cover lemmas -/

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)

include hu hs hc

/-- `lma:coverK1`: one near pair. -/
theorem cover_k1 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn0 : mval y 0 ≤ -(9 : ℝ) / 10) (hf1 : -(9 : ℝ) / 10 < mval y 1) :
    (InPC (Cell.k1a s) y ∨ InPC (Cell.k1b s) y)
      ∧ (InPC (Cell.k1a s) y ∨ InPC (Cell.k1b1 s) y ∨ InPC (Cell.k1b2 s) y) := by
  have hnear : ∀ i < 1, mval y i ≤ -(9 : ℝ) / 10 := fun i hi => by
    interval_cases i
    exact hn0
  have hfar : 1 < 4 → -(9 : ℝ) / 10 < mval y 1 := fun _ => hf1
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  by_cases hb : -(7 : ℝ) / 8 ≤ mval y 1
  · have ha : InPC (Cell.k1a s) y :=
      inPC1 hu hs hc hnear hfar le_rfl h0 (by rw [b0_eq]; linarith)
    exact ⟨Or.inl ha, Or.inl ha⟩
  · rw [not_le] at hb
    have h1 := ivl (m := mval y 1) (a := Cell.th) (b := Cell.b0) (by rw [th_eq]; linarith) (by rw [b0_eq]; linarith)
    refine ⟨Or.inr (inPC2 hu hs hc hnear hfar (by norm_num) h0 h1 (by rw [th_eq]; linarith)), ?_⟩
    by_cases hk : -(43 : ℝ) / 50 ≤ mval y 2
    · exact Or.inr (Or.inl (inPC2 hu hs hc hnear hfar (by norm_num) h0 h1 (by rw [k2_eq]; linarith)))
    · rw [not_le] at hk
      exact Or.inr (Or.inr (inPC3 hu hs hc hnear hfar (by norm_num) h0 h1
        (ivl (a := Cell.th) (b := Cell.k2) (by rw [th_eq]; linarith) (by rw [k2_eq]; linarith))
        (by rw [th_eq]; linarith)))

/-- The first `n` pairs of the chain are near if the pair `n - 1` is. -/
theorem near_of_last {n : ℕ} (hn : n ≤ 4) (h : 0 < n → mval y (n - 1) ≤ -(9 : ℝ) / 10) :
    ∀ i < n, mval y i ≤ -(9 : ℝ) / 10 := fun i hi =>
  le_trans (mval_mono hc (c := i) (d := n - 1) (by omega) (by omega)) (h (by omega))

/-- `lma:coverK2`: two near pairs. -/
theorem cover_k2 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn1 : mval y 1 ≤ -(9 : ℝ) / 10) (hf2 : -(9 : ℝ) / 10 < mval y 2) :
    InPC (Cell.k2a s) y ∨ InPC (Cell.k2b s) y := by
  have hnear := near_of_last hu hs hc (n := 2) (by norm_num) (fun _ => hn1)
  have hfar : 2 < 4 → -(9 : ℝ) / 10 < mval y 2 := fun _ => hf2
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  have h1 := ivl (m := mval y 1) (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith)
  by_cases hk : -(43 : ℝ) / 50 ≤ mval y 2
  · exact Or.inl (inPC2 hu hs hc hnear hfar le_rfl h0 h1 (by rw [k2_eq]; linarith))
  · rw [not_le] at hk
    exact Or.inr (inPC3 hu hs hc hnear hfar (by norm_num) h0 h1
      (ivl (a := Cell.th) (b := Cell.k2) (by rw [th_eq]; linarith) (by rw [k2_eq]; linarith))
      (by rw [th_eq]; linarith))

/-- A cell with two near pairs that is closed by one claim (`lma:celldomains`). -/
theorem cover_cd2 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn1 : mval y 1 ≤ -(9 : ℝ) / 10) (hf2 : -(9 : ℝ) / 10 < mval y 2) : InPC (Cell.cd 2 s) y := by
  have hnear := near_of_last hu hs hc (n := 2) (by norm_num) (fun _ => hn1)
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  exact inPC2 hu hs hc hnear (fun _ => hf2) le_rfl h0
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith)) (by rw [th_eq]; linarith)

/-- A cell with three near pairs that is closed by one claim. -/
theorem cover_cd3 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn2 : mval y 2 ≤ -(9 : ℝ) / 10) (hf3 : -(9 : ℝ) / 10 < mval y 3) : InPC (Cell.cd 3 s) y := by
  have hnear := near_of_last hu hs hc (n := 3) (by norm_num) (fun _ => hn2)
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  exact inPC3 hu hs hc hnear (fun _ => hf3) le_rfl h0
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith))
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith)) (by rw [th_eq]; linarith)

/-- A cell with four near pairs. -/
theorem cover_cd4 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn3 : mval y 3 ≤ -(9 : ℝ) / 10) : InPC (Cell.cd 4 s) y := by
  have hnear := near_of_last hu hs hc (n := 4) (by norm_num) (fun _ => hn3)
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  exact inPC4 hu hs hc hnear (fun h => absurd h (by norm_num)) le_rfl h0
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith))
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith))
    (ivl (a := s.1) (b := Cell.th) (by linarith [h0.1]) (by rw [th_eq]; linarith))

end

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)
  {k : ℕ} (hnear : ∀ i < k, mval y i ≤ -(9 : ℝ) / 10) (hfar : k < 4 → -(9 : ℝ) / 10 < mval y k)

include hu hs hc hnear hfar

/-- `lma:coverRING` with the threshold `κ = -4/5`: the first two pairs of the chain have their inner products in
`s` and `s'`, and no pair of the remaining five points is near. The third case is that the inner products of the
third and of the fourth pair of the chain are both below `κ`. -/
theorem cover_ring (hk : k ≤ 2) {s s' : ℤ × ℤ}
    (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (h1 : (s'.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (s'.2 : ℝ) / 2000) (hf2 : -(9 : ℝ) / 10 < mval y 2) :
    InPC (Cell.rga s s') y ∨ InPC (Cell.rgb s s') y ∨ (mval y 2 < -(4 : ℝ) / 5 ∧ mval y 3 < -(4 : ℝ) / 5) := by
  by_cases ha : -(4 : ℝ) / 5 ≤ mval y 2
  · exact Or.inl (inPC2 hu hs hc hnear hfar hk h0 h1 (by rw [kr_eq]; linarith))
  · rw [not_le] at ha
    by_cases hb : -(4 : ℝ) / 5 ≤ mval y 3
    · exact Or.inr (Or.inl (inPC3 hu hs hc hnear hfar (by omega) h0 h1
        (ivl (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))
        (by rw [kr_eq]; linarith)))
    · exact Or.inr (Or.inr ⟨ha, not_le.1 hb⟩)

/-- A claim with four classes of two points whose bound for the last class is `θ`. -/
theorem ring4 (hk : k ≤ 2) {s s' s2 s3 : ℤ × ℤ}
    (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (h1 : (s'.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (s'.2 : ℝ) / 2000)
    (h2 : (s2.1 : ℝ) / 2000 ≤ mval y 2 ∧ mval y 2 ≤ (s2.2 : ℝ) / 2000)
    (h3 : (s3.1 : ℝ) / 2000 ≤ mval y 3 ∧ mval y 3 ≤ (s3.2 : ℝ) / 2000) :
    InPC ⟨[s, s', s2, s3], Cell.th⟩ y :=
  inPC4 hu hs hc hnear hfar (by omega) h0 h1 h2 h3

end

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)

include hu hs hc

/-- `lma:coverK3`: three near pairs, and a grid `r, r', …` from below the inner product of the second pair up
to `θ`. -/
theorem cover_k3 {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn2 : mval y 2 ≤ -(9 : ℝ) / 10) (hf3 : -(9 : ℝ) / 10 < mval y 3) :
    ∀ (t : List ℤ) (r r' : ℤ), (r : ℝ) / 2000 ≤ mval y 1 → mval y 1 ≤ (((r' :: t).getLastD 0 : ℤ) : ℝ) / 2000 →
      ∃ c ∈ Cell.k3s s (r :: r' :: t), InPC c y := by
  have hnear := near_of_last hu hs hc (n := 3) (by norm_num) (fun _ => hn2)
  have hfar : 3 < 4 → -(9 : ℝ) / 10 < mval y 3 := fun _ => hf3
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have key : ∀ r r' : ℤ, (r : ℝ) / 2000 ≤ mval y 1 → mval y 1 ≤ (r' : ℝ) / 2000 → InPC (Cell.k3 s r r') y :=
    fun r r' a b => inPC3 hu hs hc hnear hfar le_rfl h0 (ivl a b)
      (ivl (a := r) (b := Cell.th) (by linarith) (by rw [th_eq]; linarith)) (by rw [th_eq]; linarith)
  intro t
  induction t with
  | nil =>
    intro r r' h1 h2
    exact ⟨Cell.k3 s r r', by simp [Cell.k3s], key r r' h1 (by simpa using h2)⟩
  | cons r'' t ih =>
    intro r r' h1 h2
    by_cases h : mval y 1 ≤ (r' : ℝ) / 2000
    · exact ⟨Cell.k3 s r r', by simp [Cell.k3s], key r r' h1 h⟩
    · obtain ⟨c, hcm, hin⟩ := ih r' r'' (le_of_lt (not_le.1 h)) (by simpa using h2)
      refine ⟨c, ?_, hin⟩
      show c ∈ Cell.k3 s r r' :: Cell.k3s s (r' :: r'' :: t)
      exact List.mem_cons_of_mem _ hcm

end

/-! ## The claims of the cover lemmas are in the list -/

open Cell in
theorem mem_k1_3 : ∀ j < 5, k1a (g1 j) ∈ claims54 ∧ k1b1 (g1 j) ∈ claims54 ∧ k1b2 (g1 j) ∈ claims54 := by
  decide +kernel

open Cell in
theorem mem_k1_2 : ∀ j < 7, 5 ≤ j → k1a (g1 j) ∈ claims54 ∧ k1b (g1 j) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_rg1 : ∀ j < 3, rga (g1 j) ((g1 j).1, th) ∈ claims54 ∧ rgb (g1 j) ((g1 j).1, th) ∈ claims54 := by
  decide +kernel

open Cell in
theorem mem_rgc1 : ∀ j < 3, 1 ≤ j → rgc (g1 j) ((g1 j).1, th) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_rgc0 : rgc (g1 0) (-1980, -1960) ∈ claims54 ∧ rgc (g1 0) (-1960, -1900) ∈ claims54
    ∧ rgc (g1 0) (-1900, th) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_k2 : ∀ j < 6, 3 ≤ j → k2a (g1 j) ∈ claims54 ∧ k2b (g1 j) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_cd : cd 2 (g1 6) ∈ claims54 ∧ cd 3 (g1 6) ∈ claims54 ∧ ∀ j < 7, cd 4 (g1 j) ∈ claims54 := by
  decide +kernel

open Cell in
theorem mem_k3 : ∀ j < 6, ∀ c ∈ k3s (g1 j) (grid3 j), c ∈ claims54 := by decide +kernel

open Cell in
theorem grid3_ok : ∀ j < 6, 2 ≤ (grid3 j).length ∧ (grid3 j).headD 0 = (g1 j).1 ∧ (grid3 j).getLastD 0 = th := by
  decide +kernel

open Cell in
theorem mem_l2h : (⟨[(m1, a1)], b0⟩ : PC) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l2rg : ∀ j < 7, rga (m1, a1) (g2 j) ∈ claims54 ∧ rgb (m1, a1) (g2 j) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l2rgc : ∀ j < 7, 1 ≤ j → rgc (m1, a1) (g2 j) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l2rgc0 : rgc1 (m1, a1) (g2 0) ∈ claims54 ∧ rgc2 (m1, a1) (g2 0) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l2 : ∀ j < 7, ∀ c ∈ l2 (g2 j), c ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l2u : rga (m1, a1) (th, b0) ∈ claims54 ∧ rgb (m1, a1) (th, b0) ∈ claims54
    ∧ rgc (m1, a1) (th, b0) ∈ claims54 := by decide +kernel

open Cell in
theorem mem_l3 : (⟨[(m1, a1), (m1, a1), (m1, th)], th⟩ : PC) ∈ claims54
    ∧ (⟨[(m1, a1), (m1, a1), (m1, th), (m1, th)], th⟩ : PC) ∈ claims54 := by decide +kernel

open Cell in
theorem g1_lo : ∀ j < 7, -1980 ≤ (g1 j).1 := by decide +kernel

/-! ## The slabs -/

/-- A number between `-99/100` and `-361/400` lies in a slab of the first grid. -/
theorem slab1 {m : ℝ} (h1 : -(99 : ℝ) / 100 ≤ m) (h2 : m ≤ -(361 : ℝ) / 400) :
    ∃ j < 7, (((Cell.g1 j).1 : ℤ) : ℝ) / 2000 ≤ m ∧ m ≤ (((Cell.g1 j).2 : ℤ) : ℝ) / 2000 := by
  by_cases c1 : m ≤ -(49 : ℝ) / 50
  · refine ⟨0, by norm_num, ?_⟩
    rw [show Cell.g1 0 = ((-1980 : ℤ), (-1960 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c2 : m ≤ -(97 : ℝ) / 100
  · refine ⟨1, by norm_num, ?_⟩
    rw [show Cell.g1 1 = ((-1960 : ℤ), (-1940 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c3 : m ≤ -(24 : ℝ) / 25
  · refine ⟨2, by norm_num, ?_⟩
    rw [show Cell.g1 2 = ((-1940 : ℤ), (-1920 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c4 : m ≤ -(19 : ℝ) / 20
  · refine ⟨3, by norm_num, ?_⟩
    rw [show Cell.g1 3 = ((-1920 : ℤ), (-1900 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c5 : m ≤ -(47 : ℝ) / 50
  · refine ⟨4, by norm_num, ?_⟩
    rw [show Cell.g1 4 = ((-1900 : ℤ), (-1880 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c6 : m ≤ -(23 : ℝ) / 25
  · refine ⟨5, by norm_num, ?_⟩
    rw [show Cell.g1 5 = ((-1880 : ℤ), (-1840 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  · refine ⟨6, by norm_num, ?_⟩
    rw [show Cell.g1 6 = ((-1840 : ℤ), (-1805 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith

/-- A number between `-99/100` and `-9/10` lies in a slab of the second grid. -/
theorem slab2 {m : ℝ} (h1 : -(99 : ℝ) / 100 ≤ m) (h2 : m ≤ -(9 : ℝ) / 10) :
    ∃ j < 7, (((Cell.g2 j).1 : ℤ) : ℝ) / 2000 ≤ m ∧ m ≤ (((Cell.g2 j).2 : ℤ) : ℝ) / 2000 := by
  by_cases c1 : m ≤ -(49 : ℝ) / 50
  · refine ⟨0, by norm_num, ?_⟩
    rw [show Cell.g2 0 = ((-1980 : ℤ), (-1960 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c2 : m ≤ -(97 : ℝ) / 100
  · refine ⟨1, by norm_num, ?_⟩
    rw [show Cell.g2 1 = ((-1960 : ℤ), (-1940 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c3 : m ≤ -(24 : ℝ) / 25
  · refine ⟨2, by norm_num, ?_⟩
    rw [show Cell.g2 2 = ((-1940 : ℤ), (-1920 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c4 : m ≤ -(19 : ℝ) / 20
  · refine ⟨3, by norm_num, ?_⟩
    rw [show Cell.g2 3 = ((-1920 : ℤ), (-1900 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c5 : m ≤ -(47 : ℝ) / 50
  · refine ⟨4, by norm_num, ?_⟩
    rw [show Cell.g2 4 = ((-1900 : ℤ), (-1880 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  by_cases c6 : m ≤ -(23 : ℝ) / 25
  · refine ⟨5, by norm_num, ?_⟩
    rw [show Cell.g2 5 = ((-1880 : ℤ), (-1840 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith
  · refine ⟨6, by norm_num, ?_⟩
    rw [show Cell.g2 6 = ((-1840 : ℤ), (-1800 : ℤ)) from by decide]
    constructor <;> push_cast <;> linarith

/-! ## The 54 cells -/

section

variable {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y) (hc : IsChain y 4)

include hu hs hc

/-- `lma:coverK3` for a grid that is given as a list with at least two points. -/
theorem cover_k3' {s : ℤ × ℤ} (h0 : (s.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (s.2 : ℝ) / 2000)
    (hn2 : mval y 2 ≤ -(9 : ℝ) / 10) (hf3 : -(9 : ℝ) / 10 < mval y 3) (g : List ℤ) (hlen : 2 ≤ g.length)
    (h1 : ((g.headD 0 : ℤ) : ℝ) / 2000 ≤ mval y 1) (h2 : mval y 1 ≤ ((g.getLastD 0 : ℤ) : ℝ) / 2000) :
    ∃ c ∈ Cell.k3s s g, InPC c y := by
  match g, hlen, h1, h2 with
  | r :: r' :: t, _, h1, h2 => exact cover_k3 hu hs hc h0 hn2 hf3 t r r' h1 (by simpa using h2)
  | [_], hlen, _, _ => exact absurd hlen (by simp)
  | [], hlen, _, _ => exact absurd hlen (by simp)

/-- **The cells L1-0j-kk'**: the inner product of the first pair lies in the slab `j` of the first grid. -/
theorem first_grid {j : ℕ} (hj : j < 7)
    (hs0 : (((Cell.g1 j).1 : ℤ) : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (((Cell.g1 j).2 : ℤ) : ℝ) / 2000)
    (hA : -(99 : ℝ) / 100 ≤ mval y 0) (hn0 : mval y 0 ≤ -(9 : ℝ) / 10) : ∃ c ∈ claims54, InPC c y := by
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  by_cases hf1 : -(9 : ℝ) / 10 < mval y 1
  · obtain ⟨hA2, hA3⟩ := cover_k1 hu hs hc hs0 hn0 hf1
    by_cases hj5 : j < 5
    · obtain ⟨q1, q2, q3⟩ := mem_k1_3 j hj5
      rcases hA3 with h | h | h
      · exact ⟨_, q1, h⟩
      · exact ⟨_, q2, h⟩
      · exact ⟨_, q3, h⟩
    · obtain ⟨q1, q2⟩ := mem_k1_2 j hj (by omega)
      rcases hA2 with h | h
      · exact ⟨_, q1, h⟩
      · exact ⟨_, q2, h⟩
  rw [not_lt] at hf1
  by_cases hf2 : -(9 : ℝ) / 10 < mval y 2
  · by_cases hj3 : j < 3
    · have hnear := near_of_last hu hs hc (n := 2) (by norm_num) (fun _ => hf1)
      have hfar : 2 < 4 → -(9 : ℝ) / 10 < mval y 2 := fun _ => hf2
      have h1 := ivl (m := mval y 1) (a := (Cell.g1 j).1) (b := Cell.th) (by linarith [hs0.1])
        (by rw [th_eq]; linarith)
      obtain ⟨qa, qb⟩ := mem_rg1 j hj3
      rcases cover_ring hu hs hc hnear hfar le_rfl hs0 h1 hf2 with h | h | ⟨h2, h3⟩
      · exact ⟨_, qa, h⟩
      · exact ⟨_, qb, h⟩
      · have i2 := (ivl (m := mval y 2) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))
        have i3 := (ivl (m := mval y 3) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))
        by_cases hj0 : j = 0
        · subst hj0
          obtain ⟨c1, c2, c3⟩ := mem_rgc0
          by_cases d1 : mval y 1 ≤ -(49 : ℝ) / 50
          · exact ⟨_, c1, ring4 hu hs hc hnear hfar le_rfl hs0
              (ivl (a := -1980) (b := -1960) (by push_cast; linarith) (by push_cast; linarith)) i2 i3⟩
          by_cases d2 : mval y 1 ≤ -(19 : ℝ) / 20
          · exact ⟨_, c2, ring4 hu hs hc hnear hfar le_rfl hs0
              (ivl (a := -1960) (b := -1900) (by push_cast; linarith) (by push_cast; linarith)) i2 i3⟩
          · exact ⟨_, c3, ring4 hu hs hc hnear hfar le_rfl hs0
              (ivl (a := -1900) (b := Cell.th) (by push_cast; linarith) (by rw [th_eq]; linarith)) i2 i3⟩
        · exact ⟨_, mem_rgc1 j hj3 (by omega), ring4 hu hs hc hnear hfar le_rfl hs0 h1 i2 i3⟩
    · by_cases hj6 : j < 6
      · obtain ⟨qa, qb⟩ := mem_k2 j hj6 (by omega)
        rcases cover_k2 hu hs hc hs0 hf1 hf2 with h | h
        · exact ⟨_, qa, h⟩
        · exact ⟨_, qb, h⟩
      · have hj' : j = 6 := by omega
        subst hj'
        exact ⟨_, mem_cd.1, cover_cd2 hu hs hc hs0 hf1 hf2⟩
  rw [not_lt] at hf2
  by_cases hf3 : -(9 : ℝ) / 10 < mval y 3
  · by_cases hj6 : j < 6
    · obtain ⟨e1, e2, e3⟩ := grid3_ok j hj6
      obtain ⟨c, hcm, hin⟩ := cover_k3' hu hs hc hs0 hf2 hf3 (Cell.grid3 j) e1
        (by rw [e2]; linarith [hs0.1]) (by rw [e3, th_eq]; linarith)
      exact ⟨c, mem_k3 j hj6 c hcm, hin⟩
    · have hj' : j = 6 := by omega
      subst hj'
      exact ⟨_, mem_cd.2.1, cover_cd3 hu hs hc hs0 hf2 hf3⟩
  · rw [not_lt] at hf3
    exact ⟨_, mem_cd.2.2 j hj, cover_cd4 hu hs hc hs0 hf3⟩

/-- **The cells L2-0j-kk'**: the first pair has an inner product of at most `-99/100`, and the inner product of
the second pair lies in the slab `j` of the second grid. -/
theorem second_grid {j : ℕ} (hj : j < 7)
    (hs1 : (((Cell.g2 j).1 : ℤ) : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (((Cell.g2 j).2 : ℤ) : ℝ) / 2000)
    (hA : mval y 0 ≤ -(99 : ℝ) / 100) (hn1 : mval y 1 ≤ -(9 : ℝ) / 10) : ∃ c ∈ claims54, InPC c y := by
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  have hm0 := neg_one_le_mval hu (y := y) (c := 0) (by norm_num)
  have h0 := ivl (m := mval y 0) (a := Cell.m1) (b := Cell.a1) (by rw [m1_eq]; linarith) (by rw [a1_eq]; linarith)
  by_cases hf2 : -(9 : ℝ) / 10 < mval y 2
  · have hnear := near_of_last hu hs hc (n := 2) (by norm_num) (fun _ => hn1)
    have hfar : 2 < 4 → -(9 : ℝ) / 10 < mval y 2 := fun _ => hf2
    obtain ⟨qa, qb⟩ := mem_l2rg j hj
    rcases cover_ring hu hs hc hnear hfar le_rfl h0 hs1 hf2 with h | h | ⟨h2, h3⟩
    · exact ⟨_, qa, h⟩
    · exact ⟨_, qb, h⟩
    · by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨c1, c2⟩ := mem_l2rgc0
        by_cases d : mval y 2 ≤ -(17 : ℝ) / 20
        · exact ⟨_, c1, ring4 hu hs hc hnear hfar le_rfl h0 hs1
            (ivl (a := Cell.th) (b := Cell.sg) (by rw [th_eq]; linarith) (by rw [sg_eq]; linarith)) (ivl (m := mval y 3) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))⟩
        · exact ⟨_, c2, ring4 hu hs hc hnear hfar le_rfl h0 hs1
            (ivl (a := Cell.sg) (b := Cell.kr) (by rw [sg_eq]; linarith) (by rw [kr_eq]; linarith))
            (ivl (a := Cell.sg) (b := Cell.kr) (by rw [sg_eq]; linarith) (by rw [kr_eq]; linarith))⟩
      · exact ⟨_, mem_l2rgc j hj (by omega), ring4 hu hs hc hnear hfar le_rfl h0 hs1 (ivl (m := mval y 2) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith)) (ivl (m := mval y 3) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))⟩
  rw [not_lt] at hf2
  have i2 := ivl (m := mval y 2) (a := (Cell.g2 j).1) (b := Cell.th) (by linarith [hs1.1]) (by rw [th_eq]; linarith)
  by_cases hf3 : -(9 : ℝ) / 10 < mval y 3
  · have hnear := near_of_last hu hs hc (n := 3) (by norm_num) (fun _ => hf2)
    exact ⟨⟨[(Cell.m1, Cell.a1), Cell.g2 j, ((Cell.g2 j).1, Cell.th)], Cell.th⟩,
      mem_l2 j hj _ (by simp [Cell.l2]),
      inPC3 hu hs hc hnear (fun _ => hf3) le_rfl h0 hs1 i2 (by rw [th_eq]; linarith)⟩
  · rw [not_lt] at hf3
    have hnear := near_of_last hu hs hc (n := 4) (by norm_num) (fun _ => hf3)
    have i3 := ivl (m := mval y 3) (a := (Cell.g2 j).1) (b := Cell.th) (by linarith [hs1.1])
      (by rw [th_eq]; linarith)
    exact ⟨⟨[(Cell.m1, Cell.a1), Cell.g2 j, ((Cell.g2 j).1, Cell.th), ((Cell.g2 j).1, Cell.th)], Cell.th⟩,
      mem_l2 j hj _ (by simp [Cell.l2]),
      inPC4 hu hs hc hnear (fun h => absurd h (by norm_num)) le_rfl h0 hs1 i2 i3⟩

/-- **The 54 cells** (`thm:covering`, `lma:celldomains`, the cover lemmas and `tab:cellclaims`). A chain labelling
of a separated configuration lies in the cell L3-k2 (the first two pairs have inner products of at most `-99/100`
and no other pair is near), or in the cell L0 (all inner products are at least `-361/400`), or in one of the 113
claims of the other cells. -/
theorem cells54 :
    (mval y 0 ≤ -(99 : ℝ) / 100 ∧ mval y 1 ≤ -(99 : ℝ) / 100 ∧ -(9 : ℝ) / 10 < mval y 2)
      ∨ -(361 : ℝ) / 400 ≤ mval y 0 ∨ ∃ c ∈ claims54, InPC c y := by
  have h01 := mval_mono hc (c := 0) (d := 1) (by norm_num) (by norm_num)
  have h12 := mval_mono hc (c := 1) (d := 2) (by norm_num) (by norm_num)
  have h23 := mval_mono hc (c := 2) (d := 3) (by norm_num) (by norm_num)
  by_cases hL0 : -(361 : ℝ) / 400 ≤ mval y 0
  · exact Or.inr (Or.inl hL0)
  rw [not_le] at hL0
  by_cases hA : -(99 : ℝ) / 100 ≤ mval y 0
  · obtain ⟨j, hj, hs0⟩ := slab1 hA (le_of_lt hL0)
    exact Or.inr (Or.inr (first_grid hu hs hc hj hs0 hA (by linarith)))
  rw [not_le] at hA
  have hm0 := neg_one_le_mval hu (y := y) (c := 0) (by norm_num)
  have hm1 := neg_one_le_mval hu (y := y) (c := 1) (by norm_num)
  have hm2 := neg_one_le_mval hu (y := y) (c := 2) (by norm_num)
  have hm3 := neg_one_le_mval hu (y := y) (c := 3) (by norm_num)
  have h0 := ivl (m := mval y 0) (a := Cell.m1) (b := Cell.a1) (by rw [m1_eq]; linarith) (by rw [a1_eq]; linarith)
  have hn0 : mval y 0 ≤ -(9 : ℝ) / 10 := by linarith
  have hnear1 : ∀ i < 1, mval y i ≤ -(9 : ℝ) / 10 := fun i hi => by
    interval_cases i
    exact hn0
  by_cases hB : -(7 : ℝ) / 8 ≤ mval y 1
  · exact Or.inr (Or.inr ⟨_, mem_l2h,
      inPC1 hu hs hc hnear1 (fun _ => by linarith) le_rfl h0 (by rw [b0_eq]; linarith)⟩)
  rw [not_le] at hB
  by_cases hθ1 : mval y 1 ≤ -(9 : ℝ) / 10
  · by_cases hA1 : mval y 1 ≤ -(99 : ℝ) / 100
    · by_cases h2 : mval y 2 ≤ -(9 : ℝ) / 10
      · right
        right
        have i1 := ivl (m := mval y 1) (a := Cell.m1) (b := Cell.a1) (by rw [m1_eq]; linarith)
          (by rw [a1_eq]; linarith)
        have i2 := ivl (m := mval y 2) (a := Cell.m1) (b := Cell.th) (by rw [m1_eq]; linarith)
          (by rw [th_eq]; linarith)
        obtain ⟨c3, c4⟩ := mem_l3
        by_cases hf3 : -(9 : ℝ) / 10 < mval y 3
        · have hnear := near_of_last hu hs hc (n := 3) (by norm_num) (fun _ => h2)
          exact ⟨_, c3, inPC3 hu hs hc hnear (fun _ => hf3) le_rfl h0 i1 i2 (by rw [th_eq]; linarith)⟩
        · rw [not_lt] at hf3
          have hnear := near_of_last hu hs hc (n := 4) (by norm_num) (fun _ => hf3)
          have i3 := ivl (m := mval y 3) (a := Cell.m1) (b := Cell.th) (by rw [m1_eq]; linarith)
            (by rw [th_eq]; linarith)
          exact ⟨_, c4, inPC4 hu hs hc hnear (fun h => absurd h (by norm_num)) le_rfl h0 i1 i2 i3⟩
      · exact Or.inl ⟨le_of_lt hA, hA1, not_le.1 h2⟩
    · rw [not_le] at hA1
      obtain ⟨j, hj, hs1⟩ := slab2 (le_of_lt hA1) hθ1
      exact Or.inr (Or.inr (second_grid hu hs hc hj hs1 (le_of_lt hA) hθ1))
  · rw [not_le] at hθ1
    right
    right
    have hfar : 1 < 4 → -(9 : ℝ) / 10 < mval y 1 := fun _ => hθ1
    have i1 := ivl (m := mval y 1) (a := Cell.th) (b := Cell.b0) (by rw [th_eq]; linarith) (by rw [b0_eq]; linarith)
    have hf2 : -(9 : ℝ) / 10 < mval y 2 := by linarith
    obtain ⟨qa, qb, qc⟩ := mem_l2u
    rcases cover_ring hu hs hc hnear1 hfar (by norm_num) h0 i1 hf2 with h | h | ⟨h2, h3⟩
    · exact ⟨_, qa, h⟩
    · exact ⟨_, qb, h⟩
    · exact ⟨_, qc, ring4 hu hs hc hnear1 hfar (by norm_num) h0 i1 (ivl (m := mval y 2) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith)) (ivl (m := mval y 3) (a := Cell.th) (b := Cell.kr) (by rw [th_eq]; linarith) (by rw [kr_eq]; linarith))⟩

end

/-- In a chain every inner product of two distinct points is at least that of the first pair. -/
theorem mval_zero_le {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hc : IsChain y 4) {m n : Fin 9} (hmn : m ≠ n) :
    mval y 0 ≤ inner ℝ (y m) (y n) := by
  obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * 0 := ⟨⟨0, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * 0 + 1 := ⟨⟨1, by omega⟩, rfl⟩
  rw [← mval_eq ha hb]
  exact hc 0 (by norm_num) a b ha hb m n (by omega) (by omega) hmn

/-- info: 'S3N9.cells54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms cells54

end S3N9
