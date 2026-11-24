module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Real.Basic
public import CAP.VR.Poly

/-!
# Virtual-root certificates: the columns of a weight, and a polynomial from its pair

* `maskedPoly`: the polynomial whose coefficients are the digits of a number at the monomials of a mask,
  minus the bias. Whatever the number is, the masked number minus the bias is the value of this
  polynomial (`masked_value`), its coefficients are bounded (`masked_maj`), and its monomials are those
  of the mask.
* `dgPoly`: the polynomial `∑ e, a e * X ^ (2 e)` whose coefficients are the digits of a number at the slots of
  the squares of the monomials of a mask (`dg_value`); it serves the exact parts of the weights.
* `polyOps`: the operations of the checker on polynomials.
* `residual_bound`: if the monomials of a polynomial are admissible for an injective layout, its
  coefficients are below `2 ^ W`, and its pair passes the test of the residual, then the sum of the
  absolute values of its coefficients is at most `rho`.
* `abs_evR_le`: such a polynomial is bounded by `rho` on the cube `[-1, 1] ^ 5`.
-/

@[expose] public section

namespace CAP.VR

open MvPolynomial Finset

/-! ## Layouts -/

/-- The exponent vectors that can occur in an identity of the layout. -/
def Adm (L : Lay) (e : Fin 5 →₀ ℕ) : Prop := edeg e ≤ L.D ∧ epdeg L.pm e ≤ L.Dp ∧ ecls L.pv e = 0

/-- The strides are injective on the admissible exponent vectors. -/
def LayoutInj (L : Lay) : Prop := ∀ e e', Adm L e → Adm L e' → pos L e = pos L e' → e = e'

/-- The columns of a block are polynomials with small coefficients whose squares are admissible. -/
structure BlkGood (W : ℕ) (L : Lay) (δ dp cls wb : ℕ) : Prop where
  wb1 : 1 ≤ wb
  size : maskAt 0 L δ dp cls * 2 ^ wb ≤ 2 ^ W
  deg : 2 * δ ≤ L.D
  pdeg : 2 * dp ≤ L.Dp

theorem pos_inj_HP {L : Lay} (hL : LayoutInj L) {δ dp cls : ℕ} (h1 : 2 * δ ≤ L.D) (h2 : 2 * dp ≤ L.Dp)
    {e e' : Fin 5 →₀ ℕ} (he : e ∈ (HP L δ dp cls).support) (he' : e' ∈ (HP L δ dp cls).support)
    (h : pos L e = pos L e') : e = e' := by
  obtain ⟨a1, a2, a3⟩ := HP_spec L δ dp cls e he
  obtain ⟨b1, b2, b3⟩ := HP_spec L δ dp cls e' he'
  have hadd : e + e = e + e' := by
    refine hL _ _ ⟨by rw [edeg_add]; omega, by rw [epdeg_add]; omega, by rw [ecls_add, Nat.xor_self]⟩
      ⟨by rw [edeg_add]; omega, by rw [epdeg_add]; omega, by rw [ecls_add, a3, b3, Nat.xor_self]⟩ ?_
    rw [pos_add, pos_add, h]
  exact add_left_cancel hadd

/-! ## The masked number of a column -/

/-- The polynomial of the digits of `x` at the monomials of a mask, minus the bias. -/
noncomputable def maskedPoly (W : ℕ) (L : Lay) (δ dp cls wb x : ℕ) : Poly :=
  ∑ e ∈ (HP L δ dp cls).support,
    monomial e ((((slot W x (pos L e) &&& (mask wb * coeff e (HP L δ dp cls)) : ℕ) : ℤ))
      - ((2 ^ (wb - 1) * coeff e (HP L δ dp cls) : ℕ) : ℤ))

theorem and_mod_of_lt (x A M : ℕ) (hA : A < 2 ^ M) : x &&& A = (x % 2 ^ M) &&& A := by
  have h1 : (x &&& A) % 2 ^ M = x % 2 ^ M &&& A % 2 ^ M := Nat.and_mod_two_pow
  rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_right hA)] at h1
  exact h1

/-- A sum over exponent vectors whose slots are below `m`, as a packed number. -/
theorem sum_eq_packSum (W : ℕ) (L : Lay) (m : ℕ) (S : Finset (Fin 5 →₀ ℕ)) (g : (Fin 5 →₀ ℕ) → ℕ)
    (hS : ∀ e ∈ S, pos L e < m) :
    ∑ e ∈ S, g e * 2 ^ (W * pos L e) = packSum W m (fun p => ∑ e ∈ S with pos L e = p, g e) := by
  classical
  unfold packSum
  rw [← sum_fiberwise_of_maps_to (g := pos L) (t := range m) (fun e he => mem_range.mpr (hS e he))]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_mul]
  refine sum_congr rfl fun e he => ?_
  rw [(mem_filter.mp he).2]

theorem fiber_sum {L : Lay} {S : Finset (Fin 5 →₀ ℕ)} (hinj : ∀ e ∈ S, ∀ e' ∈ S, pos L e = pos L e' → e = e')
    (g : (Fin 5 →₀ ℕ) → ℕ) {e₀ : Fin 5 →₀ ℕ} (he₀ : e₀ ∈ S) :
    ∑ e ∈ S with pos L e = pos L e₀, g e = g e₀ := by
  classical
  refine sum_eq_single_of_mem e₀ (mem_filter.mpr ⟨he₀, rfl⟩) fun b hb hne => ?_
  exact absurd (hinj b (mem_filter.mp hb).1 e₀ he₀ (mem_filter.mp hb).2) hne

/-- **The masked number is the value of a polynomial.** -/
theorem masked_value {W : ℕ} {L : Lay} (hL : LayoutInj L) {δ dp cls wb : ℕ} (hg : BlkGood W L δ dp cls wb) (x : ℕ) :
    ((x &&& (mask wb * maskAt W L δ dp cls) : ℕ) : ℤ) - ((maskAt W L δ dp cls <<< (wb - 1) : ℕ) : ℤ)
      = ev W L (maskedPoly W L δ dp cls wb x) := by
  classical
  set G := HP L δ dp cls with hG
  set S := G.support with hS
  have hinj : ∀ e ∈ S, ∀ e' ∈ S, pos L e = pos L e' → e = e' := fun e he e' he' h => pos_inj_HP hL hg.deg hg.pdeg he he' h
  set m := S.sup (pos L) + 1 with hm
  have hpos : ∀ e ∈ S, pos L e < m := fun e he => Nat.lt_succ_of_le (Finset.le_sup (f := pos L) he)
  set κ : ℕ → ℕ := fun p => ∑ e ∈ S with pos L e = p, coeff e G with hκ
  have hmono : maskAt W L δ dp cls = packSum W m κ := by
    rw [← evN_HP, evN_eq, ← sum_eq_packSum W L m S (fun e => coeff e G) hpos]
  have hcs : csum G = maskAt 0 L δ dp cls := csum_HP L δ dp cls
  have hκle : ∀ p, κ p ≤ csum G := fun p => by
    rw [csum_eq]
    exact sum_le_sum_of_subset (filter_subset _ _)
  have hκB : ∀ p, p < m → mask wb * κ p < 2 ^ W := fun p _ => by
    have h1 : mask wb * κ p ≤ mask wb * csum G := Nat.mul_le_mul_left _ (hκle p)
    have h2 := hg.size
    rw [← hcs] at h2
    rcases Nat.eq_zero_or_pos (csum G) with h0 | h0
    · rw [h0, mul_zero] at h1
      exact lt_of_le_of_lt h1 (Nat.two_pow_pos _)
    · have h3 : mask wb * csum G < 2 ^ wb * csum G := by
        refine Nat.mul_lt_mul_of_pos_right ?_ h0
        rw [mask_eq]
        exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
      rw [mul_comm (2 ^ wb)] at h3
      omega
  have hall : mask wb * maskAt W L δ dp cls = packSum W m (fun p => mask wb * κ p) := by
    rw [hmono, packSum_mul]
  have hAlt : mask wb * maskAt W L δ dp cls < 2 ^ (W * m) := by
    rw [hall]; exact packSum_lt _ _ _ hκB
  set s : ℕ → ℕ := slot W (x % 2 ^ (W * m)) with hs
  have hx : x % 2 ^ (W * m) = packSum W m s := (packSum_slot W m _ (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
  have he : x &&& (mask wb * maskAt W L δ dp cls) = packSum W m (fun p => s p &&& (mask wb * κ p)) := by
    rw [and_mod_of_lt x _ _ hAlt, hall, hx]
    exact packSum_and W m s _ (fun p _ => slot_lt _ _ _) hκB
  set g : (Fin 5 →₀ ℕ) → ℕ := fun e => s (pos L e) &&& (mask wb * coeff e G) with hg'
  have he2 : x &&& (mask wb * maskAt W L δ dp cls) = ∑ e ∈ S, g e * 2 ^ (W * pos L e) := by
    rw [he, sum_eq_packSum W L m S g hpos]
    refine packSum_congr _ _ fun p _ => ?_
    by_cases hne : (S.filter fun e => pos L e = p).Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      have hp : p = pos L e₀ := (mem_filter.mp he₀).2.symm
      have hk : κ p = coeff e₀ G := by
        rw [hκ, hp]
        exact fiber_sum hinj (fun e => coeff e G) (mem_filter.mp he₀).1
      rw [hk, hp, fiber_sum hinj g (mem_filter.mp he₀).1]
    · have hk0 : κ p = 0 := by
        rw [hκ]
        simp only
        rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      rw [hk0, mul_zero, Nat.and_zero, not_nonempty_iff_eq_empty.mp hne, sum_empty]
  have hb : maskAt W L δ dp cls <<< (wb - 1) = ∑ e ∈ S, (2 ^ (wb - 1) * coeff e G) * 2 ^ (W * pos L e) := by
    rw [Nat.shiftLeft_eq, ← evN_HP, evN_eq, mul_comm, mul_sum]
    exact sum_congr rfl fun e _ => by ring
  rw [he2, hb]
  unfold maskedPoly
  rw [map_sum]
  push_cast
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  rw [ev_monomial]
  have hsl : slot W x (pos L e) = s (pos L e) := (slot_mod W x m _ (hpos e he)).symm
  rw [hsl]
  ring

theorem csum_monomial (e : Fin 5 →₀ ℕ) (n : ℕ) : csum (monomial e n) = n := by
  unfold csum
  rw [eval_monomial]
  simp

/-- The coefficients of the polynomial of a column are dominated by the mask, multiplied by `2 ^ (wb - 1)`. -/
theorem masked_abs {W : ℕ} {L : Lay} {δ dp cls wb : ℕ} (hw : 1 ≤ wb) (x : ℕ) :
    RAbs (maskAt 0 L δ dp cls <<< (wb - 1)) (maskedPoly W L δ dp cls wb x) := by
  classical
  set G := HP L δ dp cls with hG
  refine ⟨∑ e ∈ G.support, monomial e (2 ^ (wb - 1) * coeff e G), ?_, ?_⟩
  · unfold maskedPoly
    refine Maj.sum _ _ _ fun e _ => Maj.monomial e ?_
    set c := coeff e G
    have h1 : slot W x (pos L e) &&& (mask wb * c) ≤ mask wb * c := Nat.and_le_right
    have h2 : mask wb * c + c = 2 * (2 ^ (wb - 1) * c) := by
      rw [mask_eq, two_pow_pred hw]
      have : 1 ≤ 2 * 2 ^ (wb - 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      zify [this]
      ring
    rw [abs_le]
    constructor
    · have : (0 : ℤ) ≤ ((slot W x (pos L e) &&& (mask wb * c) : ℕ) : ℤ) := Int.natCast_nonneg _
      push_cast at this ⊢
      linarith
    · have h3 : ((slot W x (pos L e) &&& (mask wb * c) : ℕ) : ℤ) ≤ ((mask wb * c : ℕ) : ℤ) := by exact_mod_cast h1
      have h4 : ((mask wb * c : ℕ) : ℤ) + c = 2 * ((2 ^ (wb - 1) * c : ℕ) : ℤ) := by exact_mod_cast h2
      have h5 : (0 : ℤ) ≤ (c : ℤ) := Int.natCast_nonneg _
      linarith
  · rw [map_sum, ← csum_HP, Nat.shiftLeft_eq, csum_eq, sum_mul]
    refine le_of_eq (sum_congr rfl fun e _ => ?_)
    rw [csum_monomial, mul_comm]

theorem masked_support {W : ℕ} {L : Lay} {δ dp cls wb x : ℕ} {e : Fin 5 →₀ ℕ}
    (he : e ∈ (maskedPoly W L δ dp cls wb x).support) : e ∈ (HP L δ dp cls).support := by
  classical
  unfold maskedPoly at he
  obtain ⟨e', he', hee⟩ := Finset.mem_biUnion.mp (support_sum he)
  have := support_monomial_subset hee
  rw [Finset.mem_singleton] at this
  rw [this]
  exact he'

/-! ## The digits at the squares of the monomials of a mask -/

/-- The polynomial `∑ e, a e * X ^ (2 e)` over the monomials of a mask, where `a e` is the digit of `d` at the slot
of `X ^ (2 e)`. -/
noncomputable def dgPoly (W : ℕ) (L : Lay) (δ dp cls wb d : ℕ) : Poly :=
  ∑ e ∈ (HP L δ dp cls).support,
    monomial (e + e) (((slot (2 * W) d (pos L e) &&& (mask wb * coeff e (HP L δ dp cls)) : ℕ) : ℤ))

/-- **The masked number at the squares is the value of a polynomial.** -/
theorem dg_value {W : ℕ} {L : Lay} (hL : LayoutInj L) {δ dp cls wb : ℕ} (hg : BlkGood W L δ dp cls wb) (x : ℕ) :
    ((x &&& (mask wb * maskAt (2 * W) L δ dp cls) : ℕ) : ℤ) = ev W L (dgPoly W L δ dp cls wb x) := by
  classical
  set G := HP L δ dp cls with hG
  set S := G.support with hS
  have hinj : ∀ e ∈ S, ∀ e' ∈ S, pos L e = pos L e' → e = e' := fun e he e' he' h => pos_inj_HP hL hg.deg hg.pdeg he he' h
  set m := S.sup (pos L) + 1 with hm
  have hpos : ∀ e ∈ S, pos L e < m := fun e he => Nat.lt_succ_of_le (Finset.le_sup (f := pos L) he)
  set κ : ℕ → ℕ := fun p => ∑ e ∈ S with pos L e = p, coeff e G with hκ
  have hmono : maskAt (2 * W) L δ dp cls = packSum (2 * W) m κ := by
    rw [← evN_HP, evN_eq, ← sum_eq_packSum (2 * W) L m S (fun e => coeff e G) hpos]
  have hcs : csum G = maskAt 0 L δ dp cls := csum_HP L δ dp cls
  have hκle : ∀ p, κ p ≤ csum G := fun p => by
    rw [csum_eq]
    exact sum_le_sum_of_subset (filter_subset _ _)
  have hWW : (2 : ℕ) ^ W ≤ 2 ^ (2 * W) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hκB : ∀ p, p < m → mask wb * κ p < 2 ^ (2 * W) := fun p _ => by
    have h1 : mask wb * κ p ≤ mask wb * csum G := Nat.mul_le_mul_left _ (hκle p)
    have h2 := hg.size
    rw [← hcs] at h2
    rcases Nat.eq_zero_or_pos (csum G) with h0 | h0
    · rw [h0, mul_zero] at h1
      exact lt_of_le_of_lt h1 (Nat.two_pow_pos _)
    · have h3 : mask wb * csum G < 2 ^ wb * csum G := by
        refine Nat.mul_lt_mul_of_pos_right ?_ h0
        rw [mask_eq]
        exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos
      rw [mul_comm (2 ^ wb)] at h3
      omega
  have hall : mask wb * maskAt (2 * W) L δ dp cls = packSum (2 * W) m (fun p => mask wb * κ p) := by
    rw [hmono, packSum_mul]
  have hAlt : mask wb * maskAt (2 * W) L δ dp cls < 2 ^ (2 * W * m) := by
    rw [hall]; exact packSum_lt _ _ _ hκB
  set s : ℕ → ℕ := slot (2 * W) (x % 2 ^ (2 * W * m)) with hs
  have hx : x % 2 ^ (2 * W * m) = packSum (2 * W) m s := (packSum_slot (2 * W) m _ (Nat.mod_lt _ (Nat.two_pow_pos _))).symm
  have he : x &&& (mask wb * maskAt (2 * W) L δ dp cls) = packSum (2 * W) m (fun p => s p &&& (mask wb * κ p)) := by
    rw [and_mod_of_lt x _ _ hAlt, hall, hx]
    exact packSum_and (2 * W) m s _ (fun p _ => slot_lt _ _ _) hκB
  set g : (Fin 5 →₀ ℕ) → ℕ := fun e => s (pos L e) &&& (mask wb * coeff e G) with hg'
  have he2 : x &&& (mask wb * maskAt (2 * W) L δ dp cls) = ∑ e ∈ S, g e * 2 ^ (2 * W * pos L e) := by
    rw [he, sum_eq_packSum (2 * W) L m S g hpos]
    refine packSum_congr _ _ fun p _ => ?_
    by_cases hne : (S.filter fun e => pos L e = p).Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      have hp : p = pos L e₀ := (mem_filter.mp he₀).2.symm
      have hk : κ p = coeff e₀ G := by
        rw [hκ, hp]
        exact fiber_sum hinj (fun e => coeff e G) (mem_filter.mp he₀).1
      rw [hk, hp, fiber_sum hinj g (mem_filter.mp he₀).1]
    · have hk0 : κ p = 0 := by
        rw [hκ]
        simp only
        rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      rw [hk0, mul_zero, Nat.and_zero, not_nonempty_iff_eq_empty.mp hne, sum_empty]
  rw [he2]
  unfold dgPoly
  rw [map_sum]
  push_cast
  refine sum_congr rfl fun e he => ?_
  rw [ev_monomial, pos_add]
  have hsl : slot (2 * W) x (pos L e) = s (pos L e) := (slot_mod (2 * W) x m _ (hpos e he)).symm
  rw [hsl]
  have e2 : 2 * W * pos L e = W * (pos L e + pos L e) := by ring
  rw [e2]

/-- The coefficients of the polynomial of the digits are dominated by the mask, multiplied by `2 ^ wb - 1`. -/
theorem dg_abs {W : ℕ} {L : Lay} {δ dp cls wb : ℕ} (x : ℕ) :
    RAbs (mask wb * maskAt 0 L δ dp cls) (dgPoly W L δ dp cls wb x) := by
  classical
  set G := HP L δ dp cls with hG
  refine ⟨∑ e ∈ G.support, monomial (e + e) (mask wb * coeff e G), ?_, ?_⟩
  · unfold dgPoly
    refine Maj.sum _ _ _ fun e _ => Maj.monomial (e + e) ?_
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast Nat.and_le_right
  · rw [map_sum, ← csum_HP, csum_eq, mul_sum]
    exact le_of_eq (sum_congr rfl fun e _ => by rw [csum_monomial])

theorem dg_support {W : ℕ} {L : Lay} {δ dp cls wb x : ℕ} {e : Fin 5 →₀ ℕ}
    (he : e ∈ (dgPoly W L δ dp cls wb x).support) : ∃ e₀ ∈ (HP L δ dp cls).support, e = e₀ + e₀ := by
  classical
  unfold dgPoly at he
  obtain ⟨e', he', hee⟩ := Finset.mem_biUnion.mp (support_sum he)
  have := support_monomial_subset hee
  rw [Finset.mem_singleton] at this
  exact ⟨e', he', this⟩

/-! ## The operations on polynomials -/

/-- The operations of the checker on polynomials. -/
noncomputable def polyOps (W : ℕ) (L : Lay) : Ops Poly where
  add := fun a b => a + b
  sub := fun a b => a - b
  mul := fun a b => a * b
  smul := fun n a => C (n : ℤ) * a
  nat := fun n => C (n : ℤ)
  mono := fun c => monomial (expo c) 1
  sq := fun δ dp cls wb col r => ∑ i ∈ range r, maskedPoly W L δ dp cls wb (col i) ^ 2
  dg := fun δ dp cls wb d => dgPoly W L δ dp cls wb d

theorem sqAbs_cast (e β : ℕ) : ((CAP.Wsos.sqAbs e β : ℕ) : ℤ) = ((e : ℤ) - β) ^ 2 := by
  show (((e - β + (β - e)) * (e - β + (β - e)) : ℕ) : ℤ) = _
  rcases le_total e β with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_mul, Nat.cast_sub h]; ring
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_mul, Nat.cast_sub h]; ring

theorem sqSum_cast (A β : ℕ) (col : ℕ → ℕ) :
    ∀ r, ((CAP.Wsos.sqSum A β col r : ℕ) : ℤ) = ∑ i ∈ range r, (((col i &&& A : ℕ) : ℤ) - β) ^ 2
  | 0 => by simp [CAP.Wsos.sqSum]
  | r + 1 => by
    rw [sum_range_succ, ← sqSum_cast A β col r, ← sqAbs_cast]
    show ((CAP.Wsos.sqSum A β col r + CAP.Wsos.sqAbs (col r &&& A) β : ℕ) : ℤ) = _
    push_cast
    rfl

/-! ## A polynomial from its pair -/

theorem packSum_modEq_sum (w m : ℕ) (f : ℕ → ℕ) : packSum w m f ≡ ∑ j ∈ range m, f j [MOD 2 ^ w - 1] := by
  have h1 : (2 : ℕ) ^ w ≡ 1 [MOD 2 ^ w - 1] := by
    have e : 2 ^ w - 1 + 1 = 2 ^ w := Nat.sub_add_cancel Nat.one_le_two_pow
    calc 2 ^ w % (2 ^ w - 1) = (2 ^ w - 1 + 1) % (2 ^ w - 1) := by rw [e]
      _ = 1 % (2 ^ w - 1) := Nat.add_mod_left _ _
  unfold packSum
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [sum_range_succ, sum_range_succ]
    have h2 : (2 : ℕ) ^ (w * m) ≡ 1 [MOD 2 ^ w - 1] := by
      rw [pow_mul]
      simpa using h1.pow m
    exact ih.add (by simpa using (Nat.ModEq.refl (f m)).mul h2)

/-- The sum of the digits of a number whose digits are small. -/
theorem digit_sum (W slots wr x : ℕ) (hW : 1 ≤ W) (hwr : wr ≤ W) (hx : x < 2 ^ (W * slots))
    (hhi : x &&& (ones W slots * (2 ^ W - 2 ^ wr)) = 0) (hs : slots * 2 ^ wr < 2 ^ W - 1) :
    (∀ j, j < slots → slot W x j < 2 ^ wr) ∧ ∑ j ∈ range slots, slot W x j = x % (2 ^ W - 1) := by
  have hxp : x = packSum W slots (slot W x) := (packSum_slot W slots x hx).symm
  have hd : ∀ j, j < slots → slot W x j < 2 ^ wr := by
    refine slots_lt_of_and_hi W wr slots (slot W x) hwr (fun j _ => slot_lt _ _ _) ?_
    rw [← hxp, ← ones_eq W slots (by omega), mul_comm]
    exact hhi
  refine ⟨hd, ?_⟩
  have h1 : ∑ j ∈ range slots, slot W x j ≤ slots * (2 ^ wr - 1) := by
    calc ∑ j ∈ range slots, slot W x j ≤ ∑ _j ∈ range slots, (2 ^ wr - 1) :=
          sum_le_sum fun j hj => Nat.le_sub_one_of_lt (hd j (mem_range.mp hj))
      _ = slots * (2 ^ wr - 1) := by simp
  have h2 : slots * (2 ^ wr - 1) ≤ slots * 2 ^ wr := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h3 := packSum_modEq_sum W slots (slot W x)
  rw [← hxp] at h3
  rw [h3, Nat.mod_eq_of_lt (by omega)]

theorem toNat_le_abs (c : ℤ) : (c.toNat : ℤ) ≤ |c| := by
  rcases le_total 0 c with h | h
  · rw [Int.toNat_of_nonneg h, abs_of_nonneg h]
  · rw [Int.toNat_of_nonpos h]; simp

/-- **A polynomial from its pair.** Let the monomials of `F` be admissible for an injective layout and have
slots below `slots`, let the coefficients of `F` be at most `B` in absolute value with `B + 2 ^ wr ≤ 2 ^ W`,
and let the pair `(P, N)` stand for `F`. If `P + Rn = N + Rp` for two numbers with `slots` digits below
`2 ^ wr`, then the absolute values of the coefficients of `F` have a sum of at most the sum of the digits of
`Rp` and `Rn`. -/
theorem residual_bound {W : ℕ} {L : Lay} (hL : LayoutInj L) {F : Poly} (hadm : ∀ e ∈ F.support, Adm L e)
    {B slots wr rho P N Rp Rn : ℕ} (hB : RAbs B F) (hpos : ∀ e ∈ F.support, pos L e < slots)
    (hev : (P : ℤ) - N = ev W L F) (hBW : B + 2 ^ wr ≤ 2 ^ W)
    (htest : resTest W slots wr rho P N Rp Rn = true) :
    ∑ e ∈ F.support, |coeff e F| ≤ (rho : ℤ) := by
  classical
  simp only [resTest, Bool.and_eq_true] at htest
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := htest
  have hPN : P + Rn = N + Rp := Nat.eq_of_beq_eq_true h1
  have hW : 1 ≤ W := Nat.le_of_ble_eq_true h2
  have hwr : wr ≤ W := Nat.le_of_ble_eq_true h3
  have hRp : Rp < 2 ^ (W * slots) := by
    have : Rp >>> (W * slots) = 0 := Nat.eq_of_beq_eq_true h4
    exact lt_of_shiftRight_eq_zero this
  have hRn : Rn < 2 ^ (W * slots) := by
    have : Rn >>> (W * slots) = 0 := Nat.eq_of_beq_eq_true h5
    exact lt_of_shiftRight_eq_zero this
  have hmask : mask W = 2 ^ W - 1 := mask_eq W
  have hhi : ∀ x : ℕ, Nat.land x (Nat.mul (ones W slots) (Nat.sub (Nat.shiftLeft 1 W) (Nat.shiftLeft 1 wr)))
      = x &&& (ones W slots * (2 ^ W - 2 ^ wr)) := fun x => by
    show x &&& (ones W slots * (1 <<< W - 1 <<< wr)) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  have hs : slots * 2 ^ wr < 2 ^ W - 1 := by
    have : slots <<< wr < mask W := by
      rw [← Nat.blt_eq]
      exact h8
    rwa [Nat.shiftLeft_eq, hmask] at this
  obtain ⟨hdp, hsp⟩ := digit_sum W slots wr Rp hW hwr hRp ((hhi Rp).symm.trans (Nat.eq_of_beq_eq_true h6)) hs
  obtain ⟨hdn, hsn⟩ := digit_sum W slots wr Rn hW hwr hRn ((hhi Rn).symm.trans (Nat.eq_of_beq_eq_true h7)) hs
  have hrho : ∑ j ∈ range slots, slot W Rp j + ∑ j ∈ range slots, slot W Rn j ≤ rho := by
    rw [hsp, hsn, ← hmask]
    exact Nat.le_of_ble_eq_true h9
  -- the coefficients of `F` as differences of natural numbers
  obtain ⟨G, hMaj, hGB⟩ := hB
  set cp : (Fin 5 →₀ ℕ) → ℕ := fun e => (coeff e F).toNat with hcp
  set cn : (Fin 5 →₀ ℕ) → ℕ := fun e => (-coeff e F).toNat with hcn
  have hc : ∀ e, coeff e F = (cp e : ℤ) - cn e := fun e => (Int.toNat_sub_toNat_neg _).symm
  have hcpB : ∀ e, cp e ≤ B := fun e => by
    have h1 := (hMaj.coeff_le e).trans (by exact_mod_cast hGB : (csum G : ℤ) ≤ B)
    exact_mod_cast (toNat_le_abs (coeff e F)).trans h1
  have hcnB : ∀ e, cn e ≤ B := fun e => by
    have h1 := (hMaj.coeff_le e).trans (by exact_mod_cast hGB : (csum G : ℤ) ≤ B)
    have h2 := toNat_le_abs (-coeff e F)
    rw [abs_neg] at h2
    exact_mod_cast h2.trans h1
  have hinj : ∀ e ∈ F.support, ∀ e' ∈ F.support, pos L e = pos L e' → e = e' :=
    fun e he e' he' h => hL e e' (hadm e he) (hadm e' he') h
  set fp : ℕ → ℕ := fun p => ∑ e ∈ F.support with pos L e = p, cp e with hfp
  set fn : ℕ → ℕ := fun p => ∑ e ∈ F.support with pos L e = p, cn e with hfn
  have hfib : ∀ (g : (Fin 5 →₀ ℕ) → ℕ), (∀ e, g e ≤ B) → ∀ p, ∑ e ∈ F.support with pos L e = p, g e ≤ B := by
    intro g hg p
    by_cases hne : (F.support.filter fun e => pos L e = p).Nonempty
    · obtain ⟨e₀, he₀⟩ := hne
      have hp : p = pos L e₀ := (mem_filter.mp he₀).2.symm
      rw [hp, fiber_sum hinj g (mem_filter.mp he₀).1]
      exact hg e₀
    · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
      exact Nat.zero_le _
  have hevF : ev W L F = (packSum W slots fp : ℤ) - packSum W slots fn := by
    rw [ev_eq, ← sum_eq_packSum W L slots F.support cp hpos, ← sum_eq_packSum W L slots F.support cn hpos]
    push_cast
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by rw [hc e]; ring
  have hRpp : Rp = packSum W slots (slot W Rp) := (packSum_slot W slots Rp hRp).symm
  have hRnn : Rn = packSum W slots (slot W Rn) := (packSum_slot W slots Rn hRn).symm
  have hkey : packSum W slots (fun p => fp p + slot W Rn p) = packSum W slots (fun p => fn p + slot W Rp p) := by
    rw [packSum_add, packSum_add, ← hRpp, ← hRnn]
    have h10 : ((packSum W slots fp : ℕ) : ℤ) - packSum W slots fn = (Rp : ℤ) - Rn := by
      rw [← hevF, ← hev]
      have : ((P + Rn : ℕ) : ℤ) = ((N + Rp : ℕ) : ℤ) := by rw [hPN]
      push_cast at this
      linarith
    have : ((packSum W slots fp + Rn : ℕ) : ℤ) = ((packSum W slots fn + Rp : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast this
  have hlt : ∀ (g : (Fin 5 →₀ ℕ) → ℕ), (∀ e, g e ≤ B) → ∀ (R : ℕ), (∀ j, j < slots → slot W R j < 2 ^ wr) →
      ∀ j, j < slots → (∑ e ∈ F.support with pos L e = j, g e) + slot W R j < 2 ^ W := fun g hg R hR j hj => by
    have := hfib g hg j
    have := hR j hj
    omega
  have hslots := packSum_injective W slots _ _ (hlt cp hcpB Rn hdn) (hlt cn hcnB Rp hdp) hkey
  -- every coefficient is a difference of two digits
  have hcoef : ∀ e ∈ F.support, |coeff e F| ≤ (slot W Rp (pos L e) : ℤ) + slot W Rn (pos L e) := by
    intro e he
    have h11 : (∑ e' ∈ F.support with pos L e' = pos L e, cp e') + slot W Rn (pos L e)
        = (∑ e' ∈ F.support with pos L e' = pos L e, cn e') + slot W Rp (pos L e) := hslots (pos L e) (hpos e he)
    rw [fiber_sum hinj cp he, fiber_sum hinj cn he] at h11
    have h12 : coeff e F = (slot W Rp (pos L e) : ℤ) - slot W Rn (pos L e) := by
      rw [hc e]
      have : ((cp e + slot W Rn (pos L e) : ℕ) : ℤ) = ((cn e + slot W Rp (pos L e) : ℕ) : ℤ) := by rw [h11]
      push_cast at this
      linarith
    rw [h12, abs_le]
    have ha : (0 : ℤ) ≤ (slot W Rp (pos L e) : ℤ) := Int.natCast_nonneg _
    have hb : (0 : ℤ) ≤ (slot W Rn (pos L e) : ℤ) := Int.natCast_nonneg _
    constructor <;> linarith
  calc ∑ e ∈ F.support, |coeff e F|
      ≤ ∑ e ∈ F.support, ((slot W Rp (pos L e) : ℤ) + slot W Rn (pos L e)) := sum_le_sum hcoef
    _ = ((∑ e ∈ F.support, (slot W Rp (pos L e) + slot W Rn (pos L e)) : ℕ) : ℤ) := by push_cast; rfl
    _ ≤ ((∑ j ∈ range slots, (slot W Rp j + slot W Rn j) : ℕ) : ℤ) := by
        refine Int.ofNat_le.mpr ?_
        rw [← sum_image (f := fun j => slot W Rp j + slot W Rn j) (g := pos L)
          (fun a ha b hb h => hinj a ha b hb h)]
        refine sum_le_sum_of_subset fun p hp => ?_
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
        exact mem_range.mpr (hpos e he)
    _ ≤ (rho : ℤ) := by
        rw [sum_add_distrib]
        exact_mod_cast hrho

/-! ## The value at a real point -/

/-- The value of a polynomial at a real point. -/
noncomputable def evR (y : Fin 5 → ℝ) : Poly →+* ℝ := eval₂Hom (Int.castRingHom ℝ) y

/-- On the cube `[-1, 1] ^ 5` a polynomial is bounded by the sum of the absolute values of its coefficients. -/
theorem abs_evR_le {y : Fin 5 → ℝ} (hy : ∀ i, |y i| ≤ 1) (F : Poly) :
    |evR y F| ≤ ((∑ e ∈ F.support, |coeff e F| : ℤ) : ℝ) := by
  have h1 : evR y F = ∑ e ∈ F.support, ((coeff e F : ℤ) : ℝ) * ∏ i, y i ^ e i := by
    show eval₂ (Int.castRingHom ℝ) y F = _
    rw [eval₂_eq']
    rfl
  rw [h1]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  push_cast
  refine sum_le_sum fun e _ => ?_
  rw [abs_mul, abs_prod]
  have h2 : ∏ i, |y i ^ e i| ≤ 1 := by
    refine prod_le_one (fun i _ => abs_nonneg _) fun i _ => ?_
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hy i)
  calc |((coeff e F : ℤ) : ℝ)| * ∏ i, |y i ^ e i| ≤ |((coeff e F : ℤ) : ℝ)| * 1 :=
        mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |((coeff e F : ℤ) : ℝ)| := mul_one _

end CAP.VR
