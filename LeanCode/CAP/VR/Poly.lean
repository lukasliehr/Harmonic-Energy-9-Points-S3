module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases
public import CAP.Core.PackedLemmas
public import CAP.VR.Kernel

/-!
# Virtual-root certificates: the polynomials behind the numbers of the checker

The checker `CAP/VR/Kernel.lean` evaluates one definition with several sets of operations. Here we give
the set of operations whose values are the polynomials themselves (`polyOps`, in `ℤ[X₀, …, X₄]`), and
the relations between a value of the checker and a polynomial:

* `RPair`: a pair `(p, n)` of natural numbers with `p - n` the value of the polynomial at the point
  `X i = 2 ^ (W * k i)`;
* `RAbs`: a bound for the sum of the absolute values of its coefficients (through a polynomial with
  natural coefficients that dominates it, `Maj`);
* `RW`: a bound for an additive weight of its monomials (the degree, the pair degree, the slot);
* `RCls`: a set that contains the parity classes of its monomials.

Each relation is compatible with the operations. The polynomial of a monomial mask is `HP`, defined by
the recursion of `maskStep`.
-/

@[expose] public section

namespace CAP.VR

open MvPolynomial Finset

/-- Polynomials in the five variables of an identity. -/
abbrev Poly := MvPolynomial (Fin 5) ℤ

/-- Polynomials with natural coefficients. -/
abbrev NPoly := MvPolynomial (Fin 5) ℕ

/-! ## Exponent vectors -/

/-- The stride of a variable. -/
def Lay.k (L : Lay) : Fin 5 → ℕ := ![L.k0, L.k1, L.k2, L.k3, L.k4]

/-- The slot of an exponent vector. -/
def pos (L : Lay) (e : Fin 5 →₀ ℕ) : ℕ := ∑ i, L.k i * e i

/-- The degree. -/
def edeg (e : Fin 5 →₀ ℕ) : ℕ := ∑ i, e i

/-- The degree in the variables of the mask `pm`. -/
def epdeg (pm : ℕ) (e : Fin 5 →₀ ℕ) : ℕ := ∑ i : Fin 5, bitAt pm i * e i

/-- The parity class. -/
def ecls (pv : ℕ) (e : Fin 5 →₀ ℕ) : ℕ :=
  (e 0 % 2 * pvAt pv 0) ^^^ (e 1 % 2 * pvAt pv 1) ^^^ (e 2 % 2 * pvAt pv 2) ^^^ (e 3 % 2 * pvAt pv 3)
    ^^^ (e 4 % 2 * pvAt pv 4)

/-- The exponent vector of the code of a monomial. -/
noncomputable def expo (c : ℕ) : Fin 5 →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => dig c i

@[simp] theorem expo_apply (c : ℕ) (i : Fin 5) : expo c i = dig c i := rfl

theorem pos_add (L : Lay) (a b : Fin 5 →₀ ℕ) : pos L (a + b) = pos L a + pos L b := by
  simp [pos, mul_add, sum_add_distrib]

theorem pos_zero (L : Lay) : pos L 0 = 0 := by simp [pos]

theorem pos_expo (L : Lay) (c : ℕ) : pos L (expo c) = posOf L c := by
  simp only [pos, Fin.sum_univ_five, expo_apply]
  rfl

theorem edeg_add (a b : Fin 5 →₀ ℕ) : edeg (a + b) = edeg a + edeg b := by
  simp [edeg, sum_add_distrib]

theorem edeg_zero : edeg 0 = 0 := by simp [edeg]

theorem edeg_expo (c : ℕ) : edeg (expo c) = degOf c := by
  simp only [edeg, Fin.sum_univ_five, expo_apply]
  rfl

theorem edeg_single (i : Fin 5) : edeg (Finsupp.single i 1) = 1 := by
  simp [edeg, Finsupp.single_apply]

theorem epdeg_add (pm : ℕ) (a b : Fin 5 →₀ ℕ) : epdeg pm (a + b) = epdeg pm a + epdeg pm b := by
  simp [epdeg, mul_add, sum_add_distrib]

theorem epdeg_zero (pm : ℕ) : epdeg pm 0 = 0 := by simp [epdeg]

theorem epdeg_expo (pm c : ℕ) : epdeg pm (expo c) = pdegOf pm c := by
  simp only [epdeg, Fin.sum_univ_five, expo_apply]
  rfl

theorem epdeg_single (pm : ℕ) (i : Fin 5) : epdeg pm (Finsupp.single i 1) = bitAt pm i := by
  simp [epdeg, Finsupp.single_apply]

theorem bitAt_le_one (m i : ℕ) : bitAt m i ≤ 1 := by
  show (m >>> i) &&& 1 ≤ 1
  exact Nat.and_le_right

theorem pvAt_lt (pv i : ℕ) : pvAt pv i < 4 := by
  show (pv >>> (2 * i)) &&& 3 < 4
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem par_mul_xor (x y π : ℕ) : (x + y) % 2 * π = (x % 2 * π) ^^^ (y % 2 * π) := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    simp [Nat.add_mod, hx, hy]

theorem ecls_add (pv : ℕ) (a b : Fin 5 →₀ ℕ) : ecls pv (a + b) = ecls pv a ^^^ ecls pv b := by
  simp only [ecls, Finsupp.add_apply, par_mul_xor]
  ac_rfl

theorem ecls_zero (pv : ℕ) : ecls pv 0 = 0 := by simp [ecls]

theorem ecls_expo (pv c : ℕ) : ecls pv (expo c) = clsOf pv c := by
  simp only [ecls, expo_apply, ← Nat.and_one_is_mod]
  rfl

theorem ecls_single (pv : ℕ) (i : Fin 5) : ecls pv (Finsupp.single i 1) = pvAt pv i := by
  fin_cases i <;> simp [ecls]

theorem xor_lt_four {a b : ℕ} (ha : a < 4) (hb : b < 4) : a ^^^ b < 4 := Nat.xor_lt_two_pow (n := 2) ha hb

theorem par_mul_lt (x : ℕ) {π : ℕ} (hπ : π < 4) : x % 2 * π < 4 := by
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;> simp [hx, hπ]

theorem ecls_lt (pv : ℕ) (e : Fin 5 →₀ ℕ) : ecls pv e < 4 := by
  unfold ecls
  exact xor_lt_four (xor_lt_four (xor_lt_four (xor_lt_four (par_mul_lt _ (pvAt_lt _ _)) (par_mul_lt _ (pvAt_lt _ _)))
    (par_mul_lt _ (pvAt_lt _ _))) (par_mul_lt _ (pvAt_lt _ _))) (par_mul_lt _ (pvAt_lt _ _))

/-! ## The value at the point of a layout -/

/-- The point at which a pair stands for a polynomial. -/
def kpt (W : ℕ) (L : Lay) (i : Fin 5) : ℤ := 2 ^ (W * L.k i)

/-- The value of a polynomial at the point of the layout. -/
noncomputable def ev (W : ℕ) (L : Lay) : Poly →+* ℤ := eval (kpt W L)

/-- The same for polynomials with natural coefficients. -/
noncomputable def evN (W : ℕ) (L : Lay) : NPoly →+* ℕ := eval fun i => 2 ^ (W * L.k i)

theorem prod_kpt (W : ℕ) (L : Lay) (e : Fin 5 →₀ ℕ) : ∏ i, kpt W L i ^ e i = 2 ^ (W * pos L e) := by
  simp only [kpt, ← pow_mul]
  rw [prod_pow_eq_pow_sum]
  congr 1
  simp only [pos, mul_sum, mul_assoc]

theorem ev_monomial (W : ℕ) (L : Lay) (e : Fin 5 →₀ ℕ) (c : ℤ) : ev W L (monomial e c) = c * 2 ^ (W * pos L e) := by
  unfold ev
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _), prod_kpt]

theorem ev_eq (W : ℕ) (L : Lay) (F : Poly) : ev W L F = ∑ e ∈ F.support, coeff e F * 2 ^ (W * pos L e) := by
  unfold ev
  rw [eval_eq']
  exact sum_congr rfl fun e _ => by rw [prod_kpt]

theorem evN_eq (W : ℕ) (L : Lay) (G : NPoly) : evN W L G = ∑ e ∈ G.support, coeff e G * 2 ^ (W * pos L e) := by
  unfold evN
  rw [eval_eq']
  refine sum_congr rfl fun e _ => ?_
  congr 1
  simp only [← pow_mul]
  rw [prod_pow_eq_pow_sum]
  congr 1
  simp only [pos, mul_sum, mul_assoc]

/-! ## Bounds for the coefficients -/

/-- The sum of the coefficients of a polynomial with natural coefficients. -/
noncomputable def csum : NPoly →+* ℕ := eval fun _ => 1

theorem coeff_le_csum (G : NPoly) (m : Fin 5 →₀ ℕ) : coeff m G ≤ csum G := by
  unfold csum
  rw [eval_eq']
  simp only [one_pow, prod_const_one, mul_one]
  by_cases hm : m ∈ G.support
  · exact single_le_sum (f := fun m => coeff m G) (fun _ _ => Nat.zero_le _) hm
  · rw [notMem_support_iff.mp hm]; exact Nat.zero_le _

theorem csum_eq (G : NPoly) : csum G = ∑ e ∈ G.support, coeff e G := by
  unfold csum
  rw [eval_eq']
  simp only [one_pow, prod_const_one, mul_one]

/-- `G` dominates `F` coefficient by coefficient. -/
def Maj (F : Poly) (G : NPoly) : Prop := ∀ m, |coeff m F| ≤ ((coeff m G : ℕ) : ℤ)

namespace Maj

variable {F F' : Poly} {G G' : NPoly}

theorem add (h : Maj F G) (h' : Maj F' G') : Maj (F + F') (G + G') := fun m => by
  rw [coeff_add, coeff_add, Nat.cast_add]
  exact (abs_add_le _ _).trans (add_le_add (h m) (h' m))

theorem neg (h : Maj F G) : Maj (-F) G := fun m => by
  rw [coeff_neg, abs_neg]; exact h m

theorem sub (h : Maj F G) (h' : Maj F' G') : Maj (F - F') (G + G') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

theorem mul (h : Maj F G) (h' : Maj F' G') : Maj (F * F') (G * G') := fun m => by
  rw [coeff_mul, coeff_mul, Nat.cast_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul, Nat.cast_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) (Nat.cast_nonneg _)

theorem C {c : ℤ} {n : ℕ} (h : |c| ≤ n) : Maj (MvPolynomial.C c) (MvPolynomial.C n) := fun m => by
  rw [coeff_C, coeff_C]
  split_ifs
  · exact h
  · simp

theorem monomial (e : Fin 5 →₀ ℕ) {c : ℤ} {n : ℕ} (h : |c| ≤ n) :
    Maj (MvPolynomial.monomial e c) (MvPolynomial.monomial e n) := fun m => by
  rw [coeff_monomial, coeff_monomial]
  split_ifs
  · exact h
  · simp

theorem zero : Maj 0 0 := fun m => by simp

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (g : ι → NPoly) (h : ∀ i ∈ s, Maj (f i) (g i)) :
    Maj (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))

theorem coeff_le (h : Maj F G) (m : Fin 5 →₀ ℕ) : |coeff m F| ≤ (csum G : ℤ) :=
  (h m).trans (by exact_mod_cast coeff_le_csum G m)

end Maj

/-! ## The relations -/

/-- The pair `(p, n)` stands for the polynomial `F`: `p - n` is its value at the point. -/
def RPair (W : ℕ) (L : Lay) (x : ℕ × ℕ) (F : Poly) : Prop := (x.1 : ℤ) - x.2 = ev W L F

/-- The sum of the absolute values of the coefficients of `F` is at most `n`. -/
def RAbs (n : ℕ) (F : Poly) : Prop := ∃ G : NPoly, Maj F G ∧ csum G ≤ n

/-- A weight of exponent vectors that is additive. -/
structure AddW (w : (Fin 5 →₀ ℕ) → ℕ) : Prop where
  zero : w 0 = 0
  add : ∀ a b, w (a + b) = w a + w b

/-- The weight of every monomial of `F` is at most `n`. -/
def RW (w : (Fin 5 →₀ ℕ) → ℕ) (n : ℕ) (F : Poly) : Prop := ∀ e ∈ F.support, w e ≤ n

/-- The set `A` contains the parity class of every monomial of `F`. -/
def RCls (pv : ℕ) (A : ℕ) (F : Poly) : Prop := ∀ e ∈ F.support, A.testBit (ecls pv e) = true

theorem addW_edeg : AddW edeg := ⟨edeg_zero, edeg_add⟩

theorem addW_epdeg (pm : ℕ) : AddW (epdeg pm) := ⟨epdeg_zero pm, epdeg_add pm⟩

theorem addW_pos (L : Lay) : AddW (pos L) := ⟨pos_zero L, pos_add L⟩

theorem maxN_eq (a b : ℕ) : maxN a b = max a b := by
  unfold maxN
  rcases h : Nat.ble a b with _ | _
  · have : ¬ a ≤ b := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; cases h
    rw [max_eq_left (by omega)]; rfl
  · rw [max_eq_right (Nat.le_of_ble_eq_true h)]; rfl

theorem mem_support_C_mul {c : ℤ} {F : Poly} {e : Fin 5 →₀ ℕ} (h : e ∈ (MvPolynomial.C c * F).support) : e ∈ F.support := by
  rw [mem_support_iff, coeff_C_mul] at h
  rw [mem_support_iff]
  exact fun h0 => h (by rw [h0, mul_zero])

theorem mem_support_mul {F G : Poly} {e : Fin 5 →₀ ℕ} (h : e ∈ (F * G).support) :
    ∃ a ∈ F.support, ∃ b ∈ G.support, e = a + b := by
  classical
  have := support_mul F G h
  rw [Finset.mem_add] at this
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

namespace RW

variable {w : (Fin 5 →₀ ℕ) → ℕ} {n m : ℕ} {F G : Poly}

theorem mono (h : RW w n F) (hnm : n ≤ m) : RW w m F := fun e he => (h e he).trans hnm

theorem add (h : RW w n F) (h' : RW w m G) : RW w (maxN n m) (F + G) := fun e he => by
  classical
  rw [maxN_eq]
  rcases Finset.mem_union.mp (support_add he) with h1 | h1
  · exact (h e h1).trans (le_max_left _ _)
  · exact (h' e h1).trans (le_max_right _ _)

theorem sub (h : RW w n F) (h' : RW w m G) : RW w (maxN n m) (F - G) := fun e he => by
  classical
  rw [maxN_eq]
  rcases Finset.mem_union.mp (support_sub _ F G he) with h1 | h1
  · exact (h e h1).trans (le_max_left _ _)
  · exact (h' e h1).trans (le_max_right _ _)

theorem mul (hw : AddW w) (h : RW w n F) (h' : RW w m G) : RW w (n + m) (F * G) := fun e he => by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_mul he
  rw [hw.add]
  exact add_le_add (h a ha) (h' b hb)

theorem smul (c : ℕ) (h : RW w n F) : RW w n (C (c : ℤ) * F) := fun e he => h e (mem_support_C_mul he)

theorem nat (hw : AddW w) (c n : ℕ) : RW w n (C (c : ℤ) : Poly) := fun e he => by
  classical
  have h1 := support_monomial_subset (s := (0 : Fin 5 →₀ ℕ)) (a := (c : ℤ)) he
  rw [Finset.mem_singleton] at h1
  rw [h1, hw.zero]
  exact Nat.zero_le _

theorem monomial (e₀ : Fin 5 →₀ ℕ) (c : ℤ) : RW w (w e₀) (monomial e₀ c : Poly) := fun e he => by
  classical
  have h1 := support_monomial_subset he
  rw [Finset.mem_singleton] at h1
  rw [h1]

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (h : ∀ i ∈ s, RW w n (f i)) : RW w n (∑ i ∈ s, f i) := fun e he => by
  classical
  obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.mp (support_sum he)
  exact h i hi e hie

end RW

/-! ## Sets of parity classes -/

/-- The test of `csetMul` on all sets and classes. -/
def csetOk : Bool :=
  (List.range 16).all fun A => (List.range 16).all fun B => (List.range 4).all fun a => (List.range 4).all fun b =>
    !(A.testBit a) || !(B.testBit b) || (csetMul A B).testBit (a ^^^ b)

theorem csetOk_true : csetOk = true := by decide +kernel

theorem csetMul_spec {A B a b : ℕ} (hA : A < 16) (hB : B < 16) (ha : a < 4) (hb : b < 4)
    (h1 : A.testBit a = true) (h2 : B.testBit b = true) : (csetMul A B).testBit (a ^^^ b) = true := by
  have h := csetOk_true
  unfold csetOk at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := h A hA B hB a ha b hb
  rw [h1, h2] at this
  simpa using this

theorem testBit_and_15 (A : ℕ) {a : ℕ} (ha : a < 4) : (A &&& 15).testBit a = A.testBit a := by
  rw [Nat.testBit_and]
  have : (15 : ℕ).testBit a = true := by
    have : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> rfl
  rw [this, Bool.and_true]

namespace RCls

variable {pv A B : ℕ} {F G : Poly}

theorem add (h : RCls pv A F) (h' : RCls pv B G) : RCls pv (A ||| B) (F + G) := fun e he => by
  classical
  rw [Nat.testBit_or]
  rcases Finset.mem_union.mp (support_add he) with h1 | h1
  · rw [h e h1, Bool.true_or]
  · rw [h' e h1, Bool.or_true]

theorem sub (h : RCls pv A F) (h' : RCls pv B G) : RCls pv (A ||| B) (F - G) := fun e he => by
  classical
  rw [Nat.testBit_or]
  rcases Finset.mem_union.mp (support_sub _ F G he) with h1 | h1
  · rw [h e h1, Bool.true_or]
  · rw [h' e h1, Bool.or_true]

theorem mul (h : RCls pv A F) (h' : RCls pv B G) : RCls pv (csetMul (A &&& 15) (B &&& 15)) (F * G) := fun e he => by
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_support_mul he
  rw [ecls_add]
  have h15 : ∀ x : ℕ, x &&& 15 < 16 := fun x => Nat.lt_succ_of_le Nat.and_le_right
  exact csetMul_spec (h15 A) (h15 B) (ecls_lt pv a) (ecls_lt pv b)
    ((testBit_and_15 A (ecls_lt pv a)).trans (h a ha)) ((testBit_and_15 B (ecls_lt pv b)).trans (h' b hb))

theorem smul (c : ℕ) (h : RCls pv A F) : RCls pv (cond (Nat.beq c 0) 0 A) (C (c : ℤ) * F) := fun e he => by
  rcases hc : Nat.beq c 0 with _ | _
  · exact h e (mem_support_C_mul he)
  · rw [Nat.eq_of_beq_eq_true hc] at he
    simp at he

theorem nat (c : ℕ) : RCls pv (cond (Nat.beq c 0) 0 1) (C (c : ℤ) : Poly) := fun e he => by
  classical
  rcases hc : Nat.beq c 0 with _ | _
  · have h1 := support_monomial_subset (s := (0 : Fin 5 →₀ ℕ)) (a := (c : ℤ)) he
    rw [Finset.mem_singleton] at h1
    rw [h1, ecls_zero]
    rfl
  · rw [Nat.eq_of_beq_eq_true hc] at he
    simp at he

theorem monomial (e₀ : Fin 5 →₀ ℕ) (c : ℤ) : RCls pv (1 <<< ecls pv e₀) (monomial e₀ c : Poly) := fun e he => by
  classical
  have h1 := support_monomial_subset he
  rw [Finset.mem_singleton] at h1
  rw [h1, Nat.one_shiftLeft, Nat.testBit_two_pow_self]

theorem sum {ι : Type*} (s : Finset ι) (f : ι → Poly) (h : ∀ i ∈ s, RCls pv A (f i)) : RCls pv A (∑ i ∈ s, f i) :=
  fun e he => by
    classical
    obtain ⟨i, hi, hie⟩ := Finset.mem_biUnion.mp (support_sum he)
    exact h i hi e hie

end RCls

/-! ## The polynomials of the monomial masks -/

/-- One variable more (the recursion of `maskStep`, in a semiring). -/
def mstep {A : Type*} [CommSemiring A] (x : A) (π f : ℕ) (H : ℕ → ℕ → ℕ → A) : ℕ → ℕ → ℕ → A
  | 0, p, c => H 0 p c
  | δ + 1, p, c => H (δ + 1) p c + if f = 1 ∧ p = 0 then 0 else x * mstep x π f H δ (p - f) (c ^^^ π)

/-- The step of the variable `i`, if it belongs to the mask `L.vm`. -/
def mvar {A : Type*} [CommSemiring A] (L : Lay) (x : A) (i : ℕ) (H : ℕ → ℕ → ℕ → A) : ℕ → ℕ → ℕ → A :=
  if bitAt L.vm i = 1 then mstep x (pvAt L.pv i) (bitAt L.pm i) H else H

/-- The sum of the monomials of degree at most `δ`, pair degree at most `p` and class `c` at the point `x`. -/
def mgen {A : Type*} [CommSemiring A] (L : Lay) (x : Fin 5 → A) : ℕ → ℕ → ℕ → A :=
  mvar L (x 4) 4 (mvar L (x 3) 3 (mvar L (x 2) 2 (mvar L (x 1) 1 (mvar L (x 0) 0 fun _ _ c => if c = 0 then 1 else 0))))

/-- The polynomial of a monomial mask. -/
noncomputable def HP (L : Lay) (δ p c : ℕ) : NPoly := mgen L (fun i => X i) δ p c

theorem forceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) : forceNat x k = k x := by cases x <;> rfl

theorem beq_and_iff (f p : ℕ) : (Nat.beq f 1 && Nat.beq p 0) = true ↔ f = 1 ∧ p = 0 := by
  rw [Bool.and_eq_true]
  exact ⟨fun h => ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩, fun h => ⟨by rw [h.1]; rfl, by rw [h.2]; rfl⟩⟩

theorem cond_beq_and {α : Type*} (f p : ℕ) (a b : α) :
    cond (Nat.beq f 1 && Nat.beq p 0) a b = if f = 1 ∧ p = 0 then a else b := by
  by_cases h : f = 1 ∧ p = 0
  · rw [(beq_and_iff f p).mpr h, if_pos h]; rfl
  · rw [Bool.eq_false_iff.mpr (mt (beq_and_iff f p).mp h), if_neg h]; rfl

theorem maskStep_succ (s π f : ℕ) (H : ℕ → ℕ → ℕ → ℕ) (δ p c : ℕ) :
    maskStep s π f H (δ + 1) p c = H (δ + 1) p c + cond (Nat.beq f 1 && Nat.beq p 0) 0
      (forceNat (p - f) (fun p' => forceNat (c ^^^ π) (fun c' => maskStep s π f H δ p' c')) <<< s) := rfl

theorem maskStep_eq (s π f : ℕ) (H : ℕ → ℕ → ℕ → ℕ) : ∀ δ p c, maskStep s π f H δ p c = mstep (2 ^ s) π f H δ p c
  | 0, _, _ => rfl
  | δ + 1, p, c => by
    rw [maskStep_succ, forceNat_eq, forceNat_eq, maskStep_eq s π f H δ, cond_beq_and, Nat.shiftLeft_eq, mstep, mul_comm]

theorem maskVar_eq (W : ℕ) (L : Lay) (i k : ℕ) (H : ℕ → ℕ → ℕ → ℕ) :
    maskVar W L i k H = mvar L (2 ^ (W * k)) i H := by
  unfold maskVar mvar
  by_cases h : bitAt L.vm i = 1
  · rw [if_pos h, show Nat.beq (bitAt L.vm i) 1 = true by rw [h]; rfl]
    funext δ p c
    exact maskStep_eq _ _ _ _ _ _ _
  · rw [if_neg h, show Nat.beq (bitAt L.vm i) 1 = false from Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')]
    rfl

theorem mask0_eq : mask0 = fun (_ _ c : ℕ) => if c = 0 then (1 : ℕ) else 0 := by
  funext _ _ c
  unfold mask0
  by_cases h : c = 0
  · rw [if_pos h, h]; rfl
  · rw [if_neg h, show Nat.beq c 0 = false from Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')]; rfl

theorem maskOf_eq (W : ℕ) (L : Lay) : maskOf W L = mgen L fun i => 2 ^ (W * L.k i) := by
  unfold maskOf mgen
  rw [maskVar_eq, maskVar_eq, maskVar_eq, maskVar_eq, maskVar_eq, mask0_eq]
  rfl

theorem maskAt_eq (W : ℕ) (L : Lay) (δ p c : ℕ) : maskAt W L δ p c = mgen L (fun i => 2 ^ (W * L.k i)) δ p c := by
  unfold maskAt
  rw [forceNat_eq, forceNat_eq, forceNat_eq, maskOf_eq]

theorem map_mstep {A B : Type*} [CommSemiring A] [CommSemiring B] (φ : A →+* B) (x : A) (π f : ℕ) (H : ℕ → ℕ → ℕ → A) :
    ∀ δ p c, φ (mstep x π f H δ p c) = mstep (φ x) π f (fun a b c => φ (H a b c)) δ p c
  | 0, _, _ => rfl
  | δ + 1, p, c => by
    rw [mstep, mstep, map_add]
    by_cases h : f = 1 ∧ p = 0
    · rw [if_pos h, if_pos h, map_zero]
    · rw [if_neg h, if_neg h, map_mul, map_mstep φ x π f H δ]

theorem map_mvar {A B : Type*} [CommSemiring A] [CommSemiring B] (φ : A →+* B) (L : Lay) (x : A) (i : ℕ) (H : ℕ → ℕ → ℕ → A)
    (δ p c : ℕ) : φ (mvar L x i H δ p c) = mvar L (φ x) i (fun a b c => φ (H a b c)) δ p c := by
  unfold mvar
  by_cases h : bitAt L.vm i = 1
  · rw [if_pos h, if_pos h, map_mstep]
  · rw [if_neg h, if_neg h]

theorem map_mgen {A B : Type*} [CommSemiring A] [CommSemiring B] (φ : A →+* B) (L : Lay) (x : Fin 5 → A) (δ p c : ℕ) :
    φ (mgen L x δ p c) = mgen L (fun i => φ (x i)) δ p c := by
  unfold mgen
  rw [map_mvar]
  congr 1
  funext δ p c
  rw [map_mvar]
  congr 1
  funext δ p c
  rw [map_mvar]
  congr 1
  funext δ p c
  rw [map_mvar]
  congr 1
  funext δ p c
  rw [map_mvar]
  congr 1
  funext _ _ c
  split_ifs <;> simp

theorem evN_HP (W : ℕ) (L : Lay) (δ p c : ℕ) : evN W L (HP L δ p c) = maskAt W L δ p c := by
  unfold HP
  rw [map_mgen, maskAt_eq]
  congr 1
  funext i
  simp [evN]

theorem csum_HP (L : Lay) (δ p c : ℕ) : csum (HP L δ p c) = maskAt 0 L δ p c := by
  unfold HP
  rw [map_mgen, maskAt_eq]
  congr 1
  funext i
  simp [csum]

/-- Every monomial of a mask has the degree, the pair degree and the class of the mask. -/
def MaskSpec (L : Lay) (H : ℕ → ℕ → ℕ → NPoly) : Prop :=
  ∀ δ p c, ∀ e ∈ (H δ p c).support, edeg e ≤ δ ∧ epdeg L.pm e ≤ p ∧ ecls L.pv e = c

theorem mem_support_X_mul {i : Fin 5} {q : NPoly} {e : Fin 5 →₀ ℕ} (h : e ∈ (X i * q).support) :
    ∃ e' ∈ q.support, e = e' + Finsupp.single i 1 := by
  classical
  rw [mem_support_iff, coeff_X_mul'] at h
  by_cases hi : i ∈ e.support
  · rw [if_pos hi] at h
    refine ⟨e - Finsupp.single i 1, mem_support_iff.mpr h, ?_⟩
    have h1 : Finsupp.single i 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    exact (tsub_add_cancel_of_le h1).symm
  · rw [if_neg hi] at h
    exact absurd rfl h

theorem mstep_spec (L : Lay) (i : Fin 5) (H : ℕ → ℕ → ℕ → NPoly) (hH : MaskSpec L H) :
    MaskSpec L (mstep (X i) (pvAt L.pv i) (bitAt L.pm i) H) := by
  classical
  intro δ
  induction δ with
  | zero => exact fun p c e he => hH 0 p c e he
  | succ δ ih =>
    intro p c e he
    rw [mstep] at he
    rcases Finset.mem_union.mp (support_add he) with h1 | h1
    · exact hH (δ + 1) p c e h1
    · by_cases hg : bitAt L.pm i = 1 ∧ p = 0
      · rw [if_pos hg] at h1
        simp at h1
      · rw [if_neg hg] at h1
        obtain ⟨e', he', rfl⟩ := mem_support_X_mul h1
        obtain ⟨h2, h3, h4⟩ := ih _ _ e' he'
        have hf := bitAt_le_one L.pm i
        refine ⟨by rw [edeg_add, edeg_single]; omega, ?_, ?_⟩
        · rw [epdeg_add, epdeg_single]
          omega
        · rw [ecls_add, ecls_single, h4, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem mvar_spec (L : Lay) (i : Fin 5) (H : ℕ → ℕ → ℕ → NPoly) (hH : MaskSpec L H) :
    MaskSpec L (mvar L (X i) i H) := by
  unfold mvar
  split_ifs
  · exact mstep_spec L i H hH
  · exact hH

theorem HP_spec (L : Lay) : MaskSpec L (HP L) := by
  have h0 : MaskSpec L (fun _ _ c => if c = 0 then (1 : NPoly) else 0) := by
    classical
    intro δ p c e he
    dsimp only at he
    by_cases hc : c = 0
    · rw [if_pos hc] at he
      have h1 : e = 0 := by
        have := support_monomial_subset (R := ℕ) (s := (0 : Fin 5 →₀ ℕ)) (a := 1) he
        exact Finset.mem_singleton.mp this
      rw [h1, edeg_zero, epdeg_zero, ecls_zero, hc]
      exact ⟨Nat.zero_le _, Nat.zero_le _, rfl⟩
    · rw [if_neg hc] at he
      simp at he
  exact mvar_spec L 4 _ (mvar_spec L 3 _ (mvar_spec L 2 _ (mvar_spec L 1 _ (mvar_spec L 0 _ h0))))

/-- Every monomial in the variables of `V` with the degree, the pair degree and the class of a mask occurs in it. -/
def MaskFull (L : Lay) (V : Fin 5 → Prop) (H : ℕ → ℕ → ℕ → NPoly) : Prop :=
  ∀ δ p c (e : Fin 5 →₀ ℕ), (∀ i, ¬ V i → e i = 0) → edeg e ≤ δ → epdeg L.pm e ≤ p → ecls L.pv e = c → 1 ≤ coeff e (H δ p c)

theorem mstep_full (L : Lay) (i : Fin 5) (V : Fin 5 → Prop) (H : ℕ → ℕ → ℕ → NPoly) (hH : MaskFull L V H) :
    MaskFull L (fun j => V j ∨ j = i) (mstep (X i) (pvAt L.pv i) (bitAt L.pm i) H) := by
  classical
  intro δ
  induction δ with
  | zero =>
    intro p c e hV hd hp hc
    have he : e = 0 := by
      ext j
      have : e j ≤ edeg e := single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _) (mem_univ j)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    exact hH 0 p c e (fun j _ => by rw [he]; rfl) hd hp hc
  | succ δ ih =>
    intro p c e hV hd hp hc
    rw [mstep, coeff_add]
    by_cases hi : e i = 0
    · have := hH (δ + 1) p c e (fun j hj => by
        by_cases hji : j = i
        · rw [hji]; exact hi
        · exact hV j (fun h => h.elim hj hji)) hd hp hc
      omega
    · have h1 : Finsupp.single i 1 ≤ e := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.mpr hi
      obtain ⟨e', rfl⟩ : ∃ e', e = e' + Finsupp.single i 1 := ⟨e - Finsupp.single i 1, (tsub_add_cancel_of_le h1).symm⟩
      rw [edeg_add, edeg_single] at hd
      rw [epdeg_add, epdeg_single] at hp
      rw [ecls_add, ecls_single] at hc
      have hf := bitAt_le_one L.pm i
      have hg : ¬ (bitAt L.pm i = 1 ∧ p = 0) := by omega
      rw [if_neg hg, add_comm e', coeff_X_mul]
      have := ih (p - bitAt L.pm i) (c ^^^ pvAt L.pv i) e' (fun j hj => by
        have := hV j hj
        rw [Finsupp.add_apply] at this
        omega) (by omega) (by omega) (by rw [← hc, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero])
      omega

theorem mvar_full (L : Lay) (i : Fin 5) (V : Fin 5 → Prop) (H : ℕ → ℕ → ℕ → NPoly) (hH : MaskFull L V H) :
    MaskFull L (fun j => V j ∨ (j = i ∧ bitAt L.vm i = 1)) (mvar L (X i) i H) := by
  unfold mvar
  by_cases h : bitAt L.vm (i : ℕ) = 1
  · rw [if_pos h]
    have := mstep_full L i V H hH
    intro δ p c e hV
    exact this δ p c e fun j hj => hV j fun h' => hj (h'.elim Or.inl fun h'' => Or.inr h''.1)
  · rw [if_neg h]
    intro δ p c e hV
    exact hH δ p c e fun j hj => hV j fun h' => h'.elim hj fun h'' => h h''.2

/-- **The masks are complete.** -/
theorem HP_full (L : Lay) (δ p c : ℕ) (e : Fin 5 →₀ ℕ) (hV : ∀ i : Fin 5, bitAt L.vm i ≠ 1 → e i = 0) (hd : edeg e ≤ δ)
    (hp : epdeg L.pm e ≤ p) (hc : ecls L.pv e = c) : 1 ≤ coeff e (HP L δ p c) := by
  have h0 : MaskFull L (fun _ => False) (fun _ _ c => if c = 0 then (1 : NPoly) else 0) := by
    intro δ p c e hV _ _ hc
    have he : e = 0 := by
      ext j
      exact hV j fun h => h
    rw [he, ecls_zero] at hc
    show 1 ≤ coeff e (if c = 0 then (1 : NPoly) else 0)
    rw [he, if_pos hc.symm]
    simp
  have h := mvar_full L 4 _ _ (mvar_full L 3 _ _ (mvar_full L 2 _ _ (mvar_full L 1 _ _ (mvar_full L 0 _ _ h0))))
  refine h δ p c e (fun j hj => hV j fun hb => hj ?_) hd hp hc
  fin_cases j
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, hb⟩))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨rfl, hb⟩)))
  · exact Or.inl (Or.inl (Or.inr ⟨rfl, hb⟩))
  · exact Or.inl (Or.inr ⟨rfl, hb⟩)
  · exact Or.inr ⟨rfl, hb⟩

end CAP.VR
