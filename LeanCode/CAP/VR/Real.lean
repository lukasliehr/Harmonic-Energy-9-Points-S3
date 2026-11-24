module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import CAP.VR.Sound

/-!
# Virtual-root certificates: the values of the checker at real points

The generic functions of the checker (`CAP/VR/Kernel.lean`), evaluated with the operations `realOps` on real
numbers, are described by ordinary real expressions:

* a polynomial in the two coordinates of a point is `poly2` (`dotS_real`), with the signs of the coordinates;
* the minorant in the Horner form is `hsum` (`hornerGo_real`, `poly2_iota`);
* the list `qList` consists of the scaled values `Qr` of the recursion of the two-root kernels, and the
  kernel term of a record is `2 ^ E1 * kernR …` (`kernGo_real`); the kernel term of a label likewise
  (`clsDeltaGo_real`);
* a block of the kernel is `∑ columns, ψ₁ * ψ₂` (`blkBil_real`, `innerK_real`);
* the sum-of-squares side is nonnegative where the weights are (`sosGo_nonneg`).
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)

variable {W : ℕ} {L : Lay} {y : Fin 5 → ℝ}

/-! ## The operations -/

/-- The monomial with the exponents `dig c 0, …, dig c 4` at the point `y`. -/
noncomputable def monoV (y : Fin 5 → ℝ) (c : ℕ) : ℝ :=
  y 0 ^ dig c 0 * y 1 ^ dig c 1 * y 2 ^ dig c 2 * y 3 ^ dig c 3 * y 4 ^ dig c 4

theorem real_add (a b : ℝ) : (realOps W L y).add a b = a + b := rfl
theorem real_sub (a b : ℝ) : (realOps W L y).sub a b = a - b := rfl
theorem real_mul (a b : ℝ) : (realOps W L y).mul a b = a * b := rfl
theorem real_smul (n : ℕ) (a : ℝ) : (realOps W L y).smul n a = (n : ℝ) * a := rfl
theorem real_nat (n : ℕ) : (realOps W L y).nat n = (n : ℝ) := rfl
theorem real_mono (c : ℕ) : (realOps W L y).mono c = monoV y c := rfl

theorem lt_of_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by
  rw [← Nat.blt_eq]
  exact h

theorem cast_shl1 (n : ℕ) : ((Nat.shiftLeft 1 n : ℕ) : ℝ) = 2 ^ n := by
  rw [show Nat.shiftLeft 1 n = 2 ^ n from Nat.one_shiftLeft n]
  norm_num

theorem cast_shl (a n : ℕ) : ((Nat.shiftLeft a n : ℕ) : ℝ) = a * 2 ^ n := by
  rw [show Nat.shiftLeft a n = a * 2 ^ n from Nat.shiftLeft_eq a n]
  norm_num

theorem len_eq : ∀ l : List ℕ, len l = l.length
  | [] => rfl
  | _ :: l => congrArg Nat.succ (len_eq l)

/-! ## The variables -/

theorem dig_var0 : dig (Nat.shiftLeft 1 (Nat.mul 4 0)) 0 = 1 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 0)) 1 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 0)) 2 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 0)) 3 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 0)) 4 = 0 := by decide

theorem dig_var1 : dig (Nat.shiftLeft 1 (Nat.mul 4 1)) 0 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 1)) 1 = 1
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 1)) 2 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 1)) 3 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 1)) 4 = 0 := by decide

theorem dig_var2 : dig (Nat.shiftLeft 1 (Nat.mul 4 2)) 0 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 2)) 1 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 2)) 2 = 1 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 2)) 3 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 2)) 4 = 0 := by decide

theorem dig_var3 : dig (Nat.shiftLeft 1 (Nat.mul 4 3)) 0 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 3)) 1 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 3)) 2 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 3)) 3 = 1
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 3)) 4 = 0 := by decide

theorem dig_var4 : dig (Nat.shiftLeft 1 (Nat.mul 4 4)) 0 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 4)) 1 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 4)) 2 = 0 ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 4)) 3 = 0
    ∧ dig (Nat.shiftLeft 1 (Nat.mul 4 4)) 4 = 1 := by decide

theorem var0 : var (realOps W L y) 0 = y 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_var0
  show monoV y (Nat.shiftLeft 1 (Nat.mul 4 0)) = y 0
  unfold monoV
  rw [h0, h1, h2, h3, h4]
  simp

theorem var1 : var (realOps W L y) 1 = y 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_var1
  show monoV y (Nat.shiftLeft 1 (Nat.mul 4 1)) = y 1
  unfold monoV
  rw [h0, h1, h2, h3, h4]
  simp

theorem var2 : var (realOps W L y) 2 = y 2 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_var2
  show monoV y (Nat.shiftLeft 1 (Nat.mul 4 2)) = y 2
  unfold monoV
  rw [h0, h1, h2, h3, h4]
  simp

theorem var3 : var (realOps W L y) 3 = y 3 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_var3
  show monoV y (Nat.shiftLeft 1 (Nat.mul 4 3)) = y 3
  unfold monoV
  rw [h0, h1, h2, h3, h4]
  simp

theorem var4 : var (realOps W L y) 4 = y 4 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_var4
  show monoV y (Nat.shiftLeft 1 (Nat.mul 4 4)) = y 4
  unfold monoV
  rw [h0, h1, h2, h3, h4]
  simp

/-! ## Polynomials in the two coordinates of a point -/

/-- The monomial `a ^ i * b ^ j` with the exponents `c = i + 16 * j`. -/
noncomputable def mono2 (c : ℕ) (a b : ℝ) : ℝ := a ^ Nat.land c 15 * b ^ Nat.shiftRight c 4

/-- The two coordinates of a point are the variables `ip` and `iq` of `y`, with the values `a` and `b`. -/
def At (y : Fin 5 → ℝ) (ip iq : ℕ) (a b : ℝ) : Prop := ∀ c, c < 256 → monoV y (codeAt ip iq c) = mono2 c a b

theorem dig_code01 : ∀ c, c < 256 → dig (codeAt 0 1 c) 0 = Nat.land c 15 ∧ dig (codeAt 0 1 c) 1 = Nat.shiftRight c 4
    ∧ dig (codeAt 0 1 c) 2 = 0 ∧ dig (codeAt 0 1 c) 3 = 0 ∧ dig (codeAt 0 1 c) 4 = 0 := by decide +kernel

theorem dig_code23 : ∀ c, c < 256 → dig (codeAt 2 3 c) 0 = 0 ∧ dig (codeAt 2 3 c) 1 = 0
    ∧ dig (codeAt 2 3 c) 2 = Nat.land c 15 ∧ dig (codeAt 2 3 c) 3 = Nat.shiftRight c 4 ∧ dig (codeAt 2 3 c) 4 = 0 := by
  decide +kernel

theorem dig_code24 : ∀ c, c < 256 → dig (codeAt 2 4 c) 0 = 0 ∧ dig (codeAt 2 4 c) 1 = 0
    ∧ dig (codeAt 2 4 c) 2 = Nat.land c 15 ∧ dig (codeAt 2 4 c) 3 = 0 ∧ dig (codeAt 2 4 c) 4 = Nat.shiftRight c 4 := by
  decide +kernel

theorem dig_code34 : ∀ c, c < 256 → dig (codeAt 3 4 c) 0 = 0 ∧ dig (codeAt 3 4 c) 1 = 0
    ∧ dig (codeAt 3 4 c) 2 = 0 ∧ dig (codeAt 3 4 c) 3 = Nat.land c 15 ∧ dig (codeAt 3 4 c) 4 = Nat.shiftRight c 4 := by
  decide +kernel

theorem dig_code40 : ∀ c, c < 256 → dig (codeAt 4 0 c) 0 = Nat.shiftRight c 4 ∧ dig (codeAt 4 0 c) 1 = 0
    ∧ dig (codeAt 4 0 c) 2 = 0 ∧ dig (codeAt 4 0 c) 3 = 0 ∧ dig (codeAt 4 0 c) 4 = Nat.land c 15 := by
  decide +kernel

theorem at01 (y : Fin 5 → ℝ) : At y 0 1 (y 0) (y 1) := fun c hc => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_code01 c hc
  unfold monoV mono2
  rw [h0, h1, h2, h3, h4]
  simp

theorem at23 (y : Fin 5 → ℝ) : At y 2 3 (y 2) (y 3) := fun c hc => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_code23 c hc
  unfold monoV mono2
  rw [h0, h1, h2, h3, h4]
  simp

theorem at24 (y : Fin 5 → ℝ) : At y 2 4 (y 2) (y 4) := fun c hc => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_code24 c hc
  unfold monoV mono2
  rw [h0, h1, h2, h3, h4]
  simp

theorem at34 (y : Fin 5 → ℝ) : At y 3 4 (y 3) (y 4) := fun c hc => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_code34 c hc
  unfold monoV mono2
  rw [h0, h1, h2, h3, h4]
  simp

theorem at40 (y : Fin 5 → ℝ) : At y 4 0 (y 4) (y 0) := fun c hc => by
  obtain ⟨h0, h1, h2, h3, h4⟩ := dig_code40 c hc
  unfold monoV mono2
  rw [h0, h1, h2, h3, h4]
  simp [mul_comm]

/-- The monomials of a list of exponents at `(a, b)`. -/
noncomputable def featL (codes : List ℕ) (a b : ℝ) : List ℝ := codes.map (fun c => mono2 c a b)

theorem monoListAt_real {ip iq : ℕ} {a b : ℝ} (hm : At y ip iq a b) :
    ∀ codes : List ℕ, (∀ c ∈ codes, c < 256) → monoListAt (realOps W L y) ip iq codes = featL codes a b
  | [], _ => rfl
  | c :: l, h => by
    show monoV y (codeAt ip iq c) :: monoListAt (realOps W L y) ip iq l = mono2 c a b :: featL l a b
    rw [hm c (h c (by simp)), monoListAt_real hm l (fun d hd => h d (List.mem_cons_of_mem _ hd))]

theorem codesOk_lt : ∀ l : List ℕ, codesOk l = true → ∀ c ∈ l, c < 256
  | [], _, c, hc => by simp at hc
  | a :: l, h, c, hc => by
    have h' : (Nat.blt a 256 && codesOk l) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hc with rfl | hc
    · exact lt_of_blt h'.1
    · exact codesOk_lt l h'.2 c hc

/-- `∑ c, ((digit of Np) - (digit of Nn)) * m c` over a list of exponents. -/
noncomputable def polyG (w : ℕ) (m : ℕ → ℝ) : List ℕ → ℕ → ℕ → ℝ
  | [], _, _ => 0
  | c :: l, Np, Nn =>
    (((Nat.land Np (mask w) : ℕ) : ℝ) - ((Nat.land Nn (mask w) : ℕ) : ℝ)) * m c
      + polyG w m l (Nat.shiftRight Np w) (Nat.shiftRight Nn w)

/-- The polynomial with the exponents `codes` and the coefficients `(digit of Np) - (digit of Nn)`, at `(a, b)`. -/
noncomputable def poly2 (w : ℕ) (codes : List ℕ) (Np Nn : ℕ) (a b : ℝ) : ℝ := polyG w (fun c => mono2 c a b) codes Np Nn

theorem polyG_congr (w : ℕ) {m m' : ℕ → ℝ} : ∀ (codes : List ℕ), (∀ c ∈ codes, m c = m' c) → ∀ Np Nn,
    polyG w m codes Np Nn = polyG w m' codes Np Nn
  | [], _, _, _ => rfl
  | c :: l, h, Np, Nn => by
    show _ * m c + polyG w m l _ _ = _ * m' c + polyG w m' l _ _
    rw [h c (by simp), polyG_congr w l (fun d hd => h d (List.mem_cons_of_mem _ hd))]

theorem dotGo_real (w : ℕ) (cf : ℕ → ℕ) (fl : ℕ → Bool) : ∀ (codes : List ℕ) (Np Nn : ℕ) (P N : ℝ),
    dotGo (realOps W L y) w (mask w) cf fl codes Np Nn P N
      = P - N + polyG w (fun c => (cond (fl c) (-1) 1 : ℝ) * monoV y (cf c)) codes Np Nn
  | [], Np, Nn, P, N => by
    show P - N = P - N + 0
    ring
  | c :: l, Np, Nn, P, N => by
    have e : polyG w (fun c => (cond (fl c) (-1) 1 : ℝ) * monoV y (cf c)) (c :: l) Np Nn
        = (((Nat.land Np (mask w) : ℕ) : ℝ) - ((Nat.land Nn (mask w) : ℕ) : ℝ)) * ((cond (fl c) (-1) 1 : ℝ) * monoV y (cf c))
          + polyG w (fun c => (cond (fl c) (-1) 1 : ℝ) * monoV y (cf c)) l (Nat.shiftRight Np w) (Nat.shiftRight Nn w) := rfl
    rw [dotGo_cons, e]
    cases fl c
    · simp only [cond_false]
      rw [dotGo_real w cf fl l]
      simp only [real_add, real_smul, real_mono]
      ring
    · simp only [cond_true]
      rw [dotGo_real w cf fl l]
      simp only [real_add, real_smul, real_mono]
      ring

theorem flipBit_eq : ∀ tp, tp < 2 → ∀ tq, tq < 2 → ∀ c, c < 256 →
    flipBit tp tq c = (tp * Nat.land c 15 + tq * Nat.shiftRight c 4) % 2 := by decide +kernel

theorem flip_mono2 {tp tq c : ℕ} (htp : tp < 2) (htq : tq < 2) (hc : c < 256) (a b : ℝ) :
    (cond (Nat.beq (flipBit tp tq c) 1) (-1) 1 : ℝ) * mono2 c a b = mono2 c ((-1) ^ tp * a) ((-1) ^ tq * b) := by
  unfold mono2
  rw [flipBit_eq tp htp tq htq c hc]
  have key : ((-1 : ℝ) ^ tp) ^ Nat.land c 15 * ((-1 : ℝ) ^ tq) ^ Nat.shiftRight c 4
      = (-1) ^ ((tp * Nat.land c 15 + tq * Nat.shiftRight c 4) % 2) := by
    rw [← pow_mul, ← pow_mul, ← pow_add, neg_one_pow_eq_pow_mod_two]
  have e : ((-1 : ℝ) ^ tp * a) ^ Nat.land c 15 * ((-1 : ℝ) ^ tq * b) ^ Nat.shiftRight c 4
      = (((-1 : ℝ) ^ tp) ^ Nat.land c 15 * ((-1 : ℝ) ^ tq) ^ Nat.shiftRight c 4) * (a ^ Nat.land c 15 * b ^ Nat.shiftRight c 4) := by
    rw [mul_pow, mul_pow]
    ring
  rw [e, key]
  rcases Nat.mod_two_eq_zero_or_one (tp * Nat.land c 15 + tq * Nat.shiftRight c 4) with h | h
  · rw [h]
    show (1 : ℝ) * _ = (-1) ^ 0 * _
    rw [pow_zero]
  · rw [h]
    show (-1 : ℝ) * _ = (-1) ^ 1 * _
    rw [pow_one]

/-- **A polynomial in the two coordinates of a point**, with the signs of the coordinates. -/
theorem dotS_real {ip iq : ℕ} {a b : ℝ} (hm : At y ip iq a b) {tp tq : ℕ} (htp : tp < 2) (htq : tq < 2) (w : ℕ)
    (codes : List ℕ) (hc : ∀ c ∈ codes, c < 256) (Np Nn : ℕ) :
    dotS (realOps W L y) w tp tq ip iq codes Np Nn = poly2 w codes Np Nn ((-1) ^ tp * a) ((-1) ^ tq * b) := by
  show dotGo (realOps W L y) w (mask w) (codeAt ip iq) (fun c => Nat.beq (flipBit tp tq c) 1) codes Np Nn
    ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) = _
  rw [dotGo_real]
  unfold poly2
  rw [polyG_congr w codes (m' := fun c => mono2 c ((-1) ^ tp * a) ((-1) ^ tq * b)) (fun c hcc => by
    show (cond (Nat.beq (flipBit tp tq c) 1) (-1) 1 : ℝ) * monoV y (codeAt ip iq c) = _
    rw [hm c (hc c hcc), flip_mono2 htp htq (hc c hcc)])]
  simp

theorem dotS_real0 {ip iq : ℕ} {a b : ℝ} (hm : At y ip iq a b) (w : ℕ) (codes : List ℕ) (hc : ∀ c ∈ codes, c < 256)
    (Np Nn : ℕ) : dotS (realOps W L y) w 0 0 ip iq codes Np Nn = poly2 w codes Np Nn a b := by
  rw [dotS_real hm (by norm_num) (by norm_num) w codes hc]
  simp

/-! ## The minorant in the Horner form -/

/-- `∑ r < n, ((digit r of hp) - (digit r of hn)) * τ ^ r` -/
noncomputable def hsum (w hp hn : ℕ) (τ : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => hsum w hp hn τ r
      + (((Nat.land (Nat.shiftRight hp (Nat.mul w r)) (mask w) : ℕ) : ℝ)
        - ((Nat.land (Nat.shiftRight hn (Nat.mul w r)) (mask w) : ℕ) : ℝ)) * τ ^ r

theorem hornerGo_real (w hp hn mH : ℕ) (τ : ℝ) : ∀ (n i : ℕ) (acc : ℝ),
    2 ^ mH * hornerGo (realOps W L y) w (mask w) hp hn (2 ^ mH * τ) mH n i acc
      = 2 ^ mH * acc * (2 ^ mH * τ) ^ n + 2 ^ (mH * i) * 2 ^ (mH * n) * hsum w hp hn τ n
  | 0, i, acc => by
    show 2 ^ mH * acc = 2 ^ mH * acc * (2 ^ mH * τ) ^ 0 + 2 ^ (mH * i) * 2 ^ (mH * 0) * 0
    ring
  | r + 1, i, acc => by
    rw [hornerGo_succ, hornerGo_real w hp hn mH τ r]
    simp only [real_add, real_mul, real_smul, real_sub, real_nat, cast_shl1, hsum, Nat.mul_eq, Nat.succ_eq_add_one]
    ring

theorem iota_small : ∀ k, k < 16 → Nat.land k 15 = k ∧ Nat.shiftRight k 4 = 0 := by decide

theorem poly2_iota (w hp hn : ℕ) (a b : ℝ) : ∀ (codes : List ℕ) (k : ℕ), iotaOk codes k = true →
    poly2 w codes (Nat.shiftRight hp (Nat.mul w k)) (Nat.shiftRight hn (Nat.mul w k)) a b
      = hsum w hp hn a (k + codes.length) - hsum w hp hn a k
  | [], k, _ => by
    show (0 : ℝ) = _
    simp
  | c :: l, k, h => by
    have h' : (Nat.beq c k && Nat.blt c 16 && iotaOk l (Nat.succ k)) = true := h
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    have hck : c = k := Nat.eq_of_beq_eq_true h1
    subst hck
    obtain ⟨e1, e2⟩ := iota_small c (lt_of_blt h2)
    have ih := poly2_iota w hp hn a b l (c + 1) h3
    have s1 : Nat.shiftRight (Nat.shiftRight hp (Nat.mul w c)) w = Nat.shiftRight hp (Nat.mul w (c + 1)) := by
      show hp >>> (w * c) >>> w = hp >>> (w * (c + 1))
      rw [← Nat.shiftRight_add, Nat.mul_succ]
    have s2 : Nat.shiftRight (Nat.shiftRight hn (Nat.mul w c)) w = Nat.shiftRight hn (Nat.mul w (c + 1)) := by
      show hn >>> (w * c) >>> w = hn >>> (w * (c + 1))
      rw [← Nat.shiftRight_add, Nat.mul_succ]
    show (((Nat.land (Nat.shiftRight hp (Nat.mul w c)) (mask w) : ℕ) : ℝ)
          - ((Nat.land (Nat.shiftRight hn (Nat.mul w c)) (mask w) : ℕ) : ℝ)) * mono2 c a b
        + poly2 w l (Nat.shiftRight (Nat.shiftRight hp (Nat.mul w c)) w) (Nat.shiftRight (Nat.shiftRight hn (Nat.mul w c)) w) a b
      = _
    rw [s1, s2, ih]
    have e3 : c + (c :: l).length = c + 1 + l.length := by
      rw [List.length_cons]
      omega
    rw [e3]
    unfold mono2
    rw [e1, e2]
    show _ = hsum w hp hn a (c + 1 + l.length) - hsum w hp hn a c
    have e4 : hsum w hp hn a (c + 1) = hsum w hp hn a c
        + (((Nat.land (Nat.shiftRight hp (Nat.mul w c)) (mask w) : ℕ) : ℝ)
          - ((Nat.land (Nat.shiftRight hn (Nat.mul w c)) (mask w) : ℕ) : ℝ)) * a ^ c := rfl
    rw [e4]
    ring

/-! ## The two-root kernels -/

/-- `Re (ω ^ k)` for a complex number `ω` with the real part `H` and the square `ρ` of the modulus. -/
noncomputable def Qr (ρ H : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => H
  | k + 2 => 2 * H * Qr ρ H (k + 1) - ρ * Qr ρ H k

/-- `∑ k, q k / 4 ^ (sK k) * inner (blocks of k)`, from the index `k` on. -/
noncomputable def kernR (inner : List Blk → ℝ) (q : ℕ → ℝ) : List (List Blk) → List ℕ → ℕ → ℝ
  | [], _, _ => 0
  | blks :: l, sK, k => q k / 4 ^ hd sK * inner blks + kernR inner q l (tl sK) (k + 1)

theorem kernR_congr {inner inner' : List Blk → ℝ} {q q' : ℕ → ℝ} (hq : ∀ k, q k = q' k) :
    ∀ (bl : List (List Blk)), (∀ blks ∈ bl, inner blks = inner' blks) → ∀ (sK : List ℕ) (k : ℕ),
      kernR inner q bl sK k = kernR inner' q' bl sK k
  | [], _, _, _ => rfl
  | blks :: l, h, sK, k => by
    show q k / 4 ^ hd sK * inner blks + kernR inner q l (tl sK) (k + 1)
      = q' k / 4 ^ hd sK * inner' blks + kernR inner' q' l (tl sK) (k + 1)
    rw [hq k, h blks (by simp), kernR_congr hq l (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-! ## The blocks of the kernel -/

/-- `∑ j, (digit j of N) * ms j` -/
noncomputable def dotR (w : ℕ) : List ℝ → ℕ → ℝ
  | [], _ => 0
  | m :: l, N => ((Nat.land N (mask w) : ℕ) : ℝ) * m + dotR w l (Nat.shiftRight N w)

theorem dot_real (w : ℕ) : ∀ (ms : List ℝ) (N : ℕ) (U : ℝ), dot (realOps W L y) w (mask w) ms N U = U + dotR w ms N
  | [], _, U => by
    show U = U + 0
    ring
  | m :: l, N, U => by
    show dot (realOps W L y) w (mask w) l (Nat.shiftRight N w) (U + ((Nat.land N (mask w) : ℕ) : ℝ) * m)
      = U + (((Nat.land N (mask w) : ℕ) : ℝ) * m + dotR w l (Nat.shiftRight N w))
    rw [dot_real w l]
    ring

theorem lsumG_real : ∀ ms : List ℝ, lsumG (realOps W L y) ms = ms.sum
  | [] => by
    show ((0 : ℕ) : ℝ) = 0
    simp
  | m :: l => by
    show m + lsumG (realOps W L y) l = (m :: l).sum
    rw [lsumG_real l, List.sum_cons]

/-- The value of a column of a block of the kernel for the monomials `ms` of the features of the class `c`:
`∑ f, ((digit f of the column) - 2 ^ (wb - 1)) * ms f`. -/
noncomputable def psi (blk : Blk) (c : ℕ) (ms : List ℝ) (col : ℕ) : ℝ :=
  dotR blk.wb ms (Nat.shiftRight col (Nat.mul blk.wb (nth blk.off c))) - ((Nat.shiftLeft 1 (Nat.pred blk.wb) : ℕ) : ℝ) * ms.sum

theorem psi_nil (blk : Blk) (c col : ℕ) : psi blk c [] col = 0 := by
  unfold psi dotR
  simp

theorem colsGo_real (wb : ℕ) (ms1 ms2 : List ℝ) (o1 o2 : ℕ) : ∀ cols : List ℕ,
    colsGo (realOps W L y) wb (mask wb) ms1 ms2 o1 o2 cols
      = ((cols.map (fun col => dotR wb ms1 (Nat.shiftRight col o1) * dotR wb ms2 (Nat.shiftRight col o2))).sum,
         (cols.map (fun col => dotR wb ms1 (Nat.shiftRight col o1))).sum,
         (cols.map (fun col => dotR wb ms2 (Nat.shiftRight col o2))).sum)
  | [] => by
    show (((0 : ℕ) : ℝ), ((0 : ℕ) : ℝ), ((0 : ℕ) : ℝ)) = _
    simp
  | col :: l => by
    rw [colsGo_cons, colsGo_real wb ms1 ms2 o1 o2 l, dot_real, dot_real]
    simp only [real_add, real_mul, real_nat, List.map_cons, List.sum_cons, Nat.cast_zero, zero_add]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show _ + _ = _ + _
      ring
    · show _ + _ = _ + _
      ring
    · show _ + _ = _ + _
      ring

theorem bil_sum (β S1 S2 : ℝ) (D1 D2 : ℕ → ℝ) : ∀ cols : List ℕ,
    (cols.map (fun c => D1 c * D2 c)).sum + (cols.length : ℝ) * (β * β) * (S1 * S2)
        - β * ((cols.map D1).sum * S2 + S1 * (cols.map D2).sum)
      = (cols.map (fun c => (D1 c - β * S1) * (D2 c - β * S2))).sum
  | [] => by simp
  | c :: l => by
    have ih := bil_sum β S1 S2 D1 D2 l
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linear_combination ih

theorem isNil_eq : ∀ l : List ℕ, isNil l = true → l = []
  | [], _ => rfl
  | _ :: _, h => by
    have : false = true := h
    exact absurd this (by simp)

/-- **A block of the kernel** is the sum over its columns of the products of the values of the column at the
two end points. -/
theorem blkBil_real (blk : Blk) (c1 i1p i1q c2 i2p i2q : ℕ) :
    blkBil (realOps W L y) blk c1 i1p i1q c2 i2p i2q
      = (blk.cols.map (fun col => psi blk c1 (monoListAt (realOps W L y) i1p i1q (nthL blk.ex c1)) col
          * psi blk c2 (monoListAt (realOps W L y) i2p i2q (nthL blk.ex c2)) col)).sum := by
  unfold blkBil
  cases hn : (isNil (nthL blk.ex c1) || isNil (nthL blk.ex c2))
  · simp only [cond_false]
    rw [colsGo_real, lsumG_real, lsumG_real]
    simp only [real_add, real_sub, real_mul, real_smul, Nat.cast_mul, len_eq, Nat.mul_eq]
    have key := bil_sum ((Nat.shiftLeft 1 (Nat.pred blk.wb) : ℕ) : ℝ)
      (monoListAt (realOps W L y) i1p i1q (nthL blk.ex c1)).sum (monoListAt (realOps W L y) i2p i2q (nthL blk.ex c2)).sum
      (fun col => dotR blk.wb (monoListAt (realOps W L y) i1p i1q (nthL blk.ex c1))
        (Nat.shiftRight col (Nat.mul blk.wb (nth blk.off c1))))
      (fun col => dotR blk.wb (monoListAt (realOps W L y) i2p i2q (nthL blk.ex c2))
        (Nat.shiftRight col (Nat.mul blk.wb (nth blk.off c2)))) blk.cols
    unfold psi
    rw [← key]
    simp only [Nat.mul_eq]
  · simp only [cond_true]
    rw [Bool.or_eq_true] at hn
    have hz : ∀ col ∈ blk.cols, psi blk c1 (monoListAt (realOps W L y) i1p i1q (nthL blk.ex c1)) col
        * psi blk c2 (monoListAt (realOps W L y) i2p i2q (nthL blk.ex c2)) col = 0 := by
      intro col _
      rcases hn with h | h
      · rw [isNil_eq _ h]
        show psi blk c1 [] col * _ = 0
        rw [psi_nil, zero_mul]
      · rw [isNil_eq _ h]
        show _ * psi blk c2 [] col = 0
        rw [psi_nil, mul_zero]
    rw [List.map_congr_left hz]
    show ((0 : ℕ) : ℝ) = _
    simp

/-- The sign `0`, `1`, `-1` of the code `0`, `1`, `2`. -/
def sgnZ (s : ℕ) : ℤ := cond (Nat.beq s 0) 0 (cond (Nat.beq s 1) 1 (-1))

noncomputable def sgnR (s : ℕ) : ℝ := ((sgnZ s : ℤ) : ℝ)

theorem sgnZ_mul : ∀ s, s < 3 → ∀ t, t < 3 → sgnZ (sgnMul s t) = sgnZ s * sgnZ t := by decide

theorem sgnR_mul {s t : ℕ} (hs : s ≤ 2) (ht : t ≤ 2) : sgnR (sgnMul s t) = sgnR s * sgnR t := by
  unfold sgnR
  rw [sgnZ_mul s (by omega) t (by omega)]
  push_cast
  ring

theorem sgnOf_le (cls sg : ℕ) (blk : Blk) : sgnOf cls sg blk ≤ 2 := by
  unfold sgnOf
  simp only [Bool.cond_eq_ite]
  split_ifs <;> omega

theorem innerK_real (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) : ∀ (blks : List Blk) (acc : ℝ),
    innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks acc
      = acc + (blks.map (fun blk => sgnR (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk))
          * blkBil (realOps W L y) blk c1 i1p i1q c2 i2p i2q)).sum
  | [], acc => by
    show acc = acc + 0
    ring
  | blk :: l, acc => by
    rw [innerK_cons, innerK_real c1 s1 i1p i1q c2 s2 i2p i2q l]
    simp only [List.map_cons, List.sum_cons, sgnR, sgnZ]
    cases Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 0 <;>
      cases Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 1 <;>
      simp only [cond_true, cond_false, real_add, real_sub, Int.cast_zero, Int.cast_one, Int.cast_neg] <;> ring

theorem usedK_cons (c1 c2 : ℕ) (blk : Blk) (l : List Blk) :
    usedK c1 c2 (blk :: l) = ((!(isNil (nthL blk.ex c1)) && !(isNil (nthL blk.ex c2))) || usedK c1 c2 l) := rfl

theorem blkBil_nil {blk : Blk} {c1 c2 : ℕ} (i1p i1q i2p i2q : ℕ)
    (h : (!(isNil (nthL blk.ex c1)) && !(isNil (nthL blk.ex c2))) = false) :
    blkBil (realOps W L y) blk c1 i1p i1q c2 i2p i2q = 0 := by
  have h' : (isNil (nthL blk.ex c1) || isNil (nthL blk.ex c2)) = true := by
    cases h1 : isNil (nthL blk.ex c1) <;> cases h2 : isNil (nthL blk.ex c2) <;> simp_all
  unfold blkBil
  rw [h']
  show ((0 : ℕ) : ℝ) = 0
  simp

theorem innerK_unused (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) : ∀ (blks : List Blk), usedK c1 c2 blks = false → ∀ acc : ℝ,
    innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks acc = acc
  | [], _, _ => rfl
  | blk :: l, h, acc => by
    rw [usedK_cons, Bool.or_eq_false_iff] at h
    rw [innerK_real]
    simp only [List.map_cons, List.sum_cons]
    rw [blkBil_nil i1p i1q i2p i2q h.1, mul_zero, zero_add, ← innerK_real, innerK_unused c1 s1 i1p i1q c2 s2 i2p i2q l h.2]

theorem lenB_cons (blks : List Blk) (l : List (List Blk)) : lenB (blks :: l) = lenB l + 1 := rfl

theorem kScalesGo_cons (c1 c2 eH E1 : ℕ) (blks : List Blk) (l : List (List Blk)) (aK sK : List ℕ) (k : ℕ) :
    kScalesGo c1 c2 eH E1 (blks :: l) aK sK k
      = ((!(usedK c1 c2 blks) || Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul eH k)) (Nat.mul 2 (hd sK))) E1)
        && kScalesGo c1 c2 eH E1 l (tl aK) (tl sK) (Nat.succ k)) := rfl

/-- **The kernel term of a record.** If the scaled inner product of the two points is `H = 2 ^ eH * Hx` and
`4 ^ mT * Wt = 4 ^ eH * ρ`, then the kernel term is `2 ^ E1` times the sum over `k` of the kernels
`Qr ρ Hx k`, divided by `4 ^ (sK k)`, times the blocks of `k`. -/
theorem kernGo_real {c1 s1 i1p i1q c2 s2 i2p i2q : ℕ} {H Wt Hx ρ : ℝ} {mT eH E1 : ℕ}
    (hH : H = 2 ^ eH * Hx) (hW : 2 ^ (2 * mT) * Wt = 2 ^ (2 * eH) * ρ) :
    ∀ (bl : List (List Blk)) (aK sK : List ℕ) (k : ℕ) (prev cur acc : ℝ),
      kScalesGo c1 c2 eH E1 bl aK sK k = true →
      cur = 2 ^ (eH * k) * Qr ρ Hx k → (∀ k', k = k' + 1 → prev = 2 ^ (eH * k') * Qr ρ Hx k') →
      kernGo (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q bl (qGo (realOps W L y) H Wt mT (lenB bl) k prev cur) aK acc
        = acc + 2 ^ E1 * kernR (fun blks => innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks 0) (Qr ρ Hx) bl sK k
  | [], _, _, _, _, _, acc, _, _, _ => by
    show acc = acc + 2 ^ E1 * 0
    ring
  | blks :: l, aK, sK, k, prev, cur, acc, hs, hc, hp => by
    rw [kScalesGo_cons, Bool.and_eq_true] at hs
    rw [lenB_cons, qGo_succ, kernGo_cons]
    have hnext : (cond (Nat.beq k 0) H
        ((realOps W L y).sub ((realOps W L y).smul 2 ((realOps W L y).mul H cur))
          ((realOps W L y).smul (Nat.shiftLeft 1 (Nat.mul 2 mT)) ((realOps W L y).mul Wt prev))))
        = 2 ^ (eH * (k + 1)) * Qr ρ Hx (k + 1) := by
      cases k with
      | zero =>
        show H = 2 ^ (eH * (0 + 1)) * Qr ρ Hx (0 + 1)
        rw [hH]
        show _ = 2 ^ (eH * (0 + 1)) * Hx
        ring
      | succ k' =>
        show (2 : ℕ) * (H * cur) - ((Nat.shiftLeft 1 (Nat.mul 2 mT) : ℕ) : ℝ) * (Wt * prev) = _
        rw [cast_shl1, hc, hp k' rfl, hH]
        show _ = 2 ^ (eH * (k' + 1 + 1)) * (2 * Hx * Qr ρ Hx (k' + 1) - ρ * Qr ρ Hx k')
        have e : (2 : ℝ) ^ Nat.mul 2 mT * (Wt * (2 ^ (eH * k') * Qr ρ Hx k'))
            = (2 ^ (2 * mT) * Wt) * (2 ^ (eH * k') * Qr ρ Hx k') := by
          show (2 : ℝ) ^ (2 * mT) * _ = _
          ring
        rw [e, hW]
        push_cast
        ring
    have ih := kernGo_real (s1 := s1) (i1p := i1p) (i1q := i1q) (s2 := s2) (i2p := i2p) (i2q := i2q) hH hW l (tl aK) (tl sK) (k + 1) cur _
      (cond (usedK c1 c2 blks)
        ((realOps W L y).add acc ((realOps W L y).smul (Nat.shiftLeft 1 (hd aK))
          ((realOps W L y).mul cur (innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks ((realOps W L y).nat 0)))))
        acc) hs.2 hnext (fun k' hk' => by
          have : k = k' := Nat.succ_injective hk'
          rw [← this]
          exact hc)
    refine Eq.trans ih ?_
    show _ = acc + 2 ^ E1 * (Qr ρ Hx k / 4 ^ hd sK * innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks 0
      + kernR (fun blks => innerK (realOps W L y) c1 s1 i1p i1q c2 s2 i2p i2q blks 0) (Qr ρ Hx) l (tl sK) (k + 1))
    cases hu : usedK c1 c2 blks
    · simp only [cond_false]
      rw [innerK_unused c1 s1 i1p i1q c2 s2 i2p i2q blks hu]
      ring
    · simp only [cond_true]
      rw [hu] at hs
      have hs1 : Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul eH k)) (Nat.mul 2 (hd sK))) E1 = true := hs.1
      have hsc : hd aK + eH * k + 2 * hd sK = E1 := Nat.eq_of_beq_eq_true hs1
      have hE : (2 : ℝ) ^ E1 = 2 ^ hd aK * 2 ^ (eH * k) * 4 ^ hd sK := by
        rw [← hsc, pow_add, pow_add, pow_mul 2 2 (hd sK)]
        norm_num
      simp only [real_add, real_smul, real_mul, real_nat, cast_shl1, Nat.cast_zero]
      rw [hc, hE]
      have h4 : (4 : ℝ) ^ hd sK ≠ 0 := by positivity
      field_simp
      ring

theorem cScalesGo_cons (cls m E : ℕ) (blks : List Blk) (l : List (List Blk)) (aK sK : List ℕ) (k : ℕ) :
    cScalesGo cls m E (blks :: l) aK sK k
      = ((!(usedK cls cls blks) || Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul (Nat.mul 2 m) k)) (Nat.mul 2 (hd sK))) E)
        && cScalesGo cls m E l (tl aK) (tl sK) (Nat.succ k)) := rfl

/-- **The kernel term of a label.** -/
theorem clsDeltaGo_real {cls sg : ℕ} {Rv r : ℝ} {m E : ℕ} (hR : Rv = 2 ^ (2 * m) * r) :
    ∀ (bl : List (List Blk)) (aK sK : List ℕ) (k : ℕ) (Rk acc : ℝ),
      cScalesGo cls m E bl aK sK k = true → Rk = 2 ^ (2 * m * k) * r ^ k →
      clsDeltaGo (realOps W L y) cls sg Rv bl aK Rk acc
        = acc + 2 ^ E * kernR (fun blks => innerK (realOps W L y) cls sg 0 1 cls sg 0 1 blks 0) (fun k => r ^ k) bl sK k
  | [], _, _, _, _, acc, _, _ => by
    show acc = acc + 2 ^ E * 0
    ring
  | blks :: l, aK, sK, k, Rk, acc, hs, hk => by
    rw [cScalesGo_cons, Bool.and_eq_true] at hs
    rw [clsDeltaGo_cons]
    have ih := clsDeltaGo_real (sg := sg) hR l (tl aK) (tl sK) (k + 1) ((realOps W L y).mul Rk Rv)
      (cond (usedK cls cls blks)
        ((realOps W L y).add acc ((realOps W L y).smul (Nat.shiftLeft 1 (hd aK))
          ((realOps W L y).mul Rk (innerK (realOps W L y) cls sg 0 1 cls sg 0 1 blks ((realOps W L y).nat 0)))))
        acc) hs.2 (by
          show Rk * Rv = _
          rw [hk, hR]
          ring)
    refine Eq.trans ih ?_
    show _ = acc + 2 ^ E * (r ^ k / 4 ^ hd sK * innerK (realOps W L y) cls sg 0 1 cls sg 0 1 blks 0
      + kernR (fun blks => innerK (realOps W L y) cls sg 0 1 cls sg 0 1 blks 0) (fun k => r ^ k) l (tl sK) (k + 1))
    cases hu : usedK cls cls blks
    · simp only [cond_false]
      rw [innerK_unused cls sg 0 1 cls sg 0 1 blks hu]
      ring
    · simp only [cond_true]
      rw [hu] at hs
      have hs1 : Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul (Nat.mul 2 m) k)) (Nat.mul 2 (hd sK))) E = true := hs.1
      have hsc : hd aK + 2 * m * k + 2 * hd sK = E := Nat.eq_of_beq_eq_true hs1
      have hE : (2 : ℝ) ^ E = 2 ^ hd aK * 2 ^ (2 * m * k) * 4 ^ hd sK := by
        rw [← hsc, pow_add, pow_add, pow_mul 2 2 (hd sK)]
        norm_num
      simp only [real_add, real_smul, real_mul, real_nat, cast_shl1, Nat.cast_zero]
      rw [hk, hE]
      have h4 : (4 : ℝ) ^ hd sK ≠ 0 := by positivity
      field_simp
      ring

/-! ## The sums of squares -/

theorem sqBlocks_nonneg : ∀ bs : List WBlk, 0 ≤ sqBlocks (realOps W L y) bs
  | [] => by
    show (0 : ℝ) ≤ ((0 : ℕ) : ℝ)
    simp
  | b :: l => by
    show 0 ≤ (realOps W L y).sq b.delta b.dp b.cls b.wb b.col b.r + sqBlocks (realOps W L y) l
    exact add_nonneg (realOps_sq_nonneg y _ _ _ _ _ _) (sqBlocks_nonneg l)

theorem hdA_nonneg {l : List ℝ} (h : ∀ g ∈ l, 0 ≤ g) : 0 ≤ hdA (realOps W L y) l := by
  cases l with
  | nil =>
    show (0 : ℝ) ≤ ((0 : ℕ) : ℝ)
    simp
  | cons a t => exact h a (by simp)

theorem tlA_mem {l : List ℝ} {g : ℝ} (hg : g ∈ tlA l) : g ∈ l := by
  cases l with
  | nil => exact hg
  | cons a t => exact List.mem_cons_of_mem _ hg

/-- **The sum-of-squares side is nonnegative** where its weights are. -/
theorem sosGo_nonneg : ∀ (ws : List Weight) (locs : List ℝ) (acc : ℝ), (∀ g ∈ locs, 0 ≤ g) → 0 ≤ acc →
    0 ≤ sosGo (realOps W L y) ws locs acc
  | [], _, _, _, ha => ha
  | w :: l, locs, acc, hl, ha => by
    rw [sosGo_cons]
    refine sosGo_nonneg l _ _ (fun g hg => hl g (tlA_mem hg)) ?_
    show 0 ≤ acc + ((Nat.shiftLeft 1 w.a : ℕ) : ℝ) * (hdA (realOps W L y) locs * sqBlocks (realOps W L y) w.blocks)
    exact add_nonneg ha (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hdA_nonneg hl) (sqBlocks_nonneg _)))

/-! ## The exchange terms of a label -/

theorem clsPhiGo_real (P : Par) (heads : List RecH) (l : ℕ) : ∀ (n : ℕ) (acc : ℝ),
    clsPhiGo (realOps W L y) P heads l n acc
      = acc + ∑ ot ∈ Finset.range n, if ot = l then 0 else piTerm (realOps W L y) P heads l ot
  | 0, acc => by
    show acc = acc + _
    simp
  | n + 1, acc => by
    rw [clsPhiGo_succ, clsPhiGo_real P heads l n, Finset.sum_range_succ]
    by_cases h : n = l
    · have hb : Nat.beq n l = true := by
        rw [h]
        exact Nat.beq_refl l
      rw [hb, if_pos h]
      show acc + _ = _
      ring
    · have hb : Nat.beq n l = false := by
        cases hbb : Nat.beq n l
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true hbb) h
      rw [hb, if_neg h]
      show acc + piTerm (realOps W L y) P heads l n + _ = _
      ring

end CAP.VR
