module

public import CAP.VR.Columns

/-!
# Virtual-root certificates: the layouts

The strides of a layout are injective on the admissible monomials only (degree at most `D`, pair degree at most
`Dp`, parity class zero). The kernel tests this (`layoutOk`): it forms the number of the sum of all admissible
monomials at a small slot width and tests that every digit is `0` or `1`. Two admissible monomials in one slot
would give a digit of at least `2` (`layoutOk_sound`; the mask polynomial contains every admissible monomial,
`HP_full`).

The six layouts of the certificates with margin of T8 are injective: `ring10_inj`, `ar10_inj`, `br10_inj`,
`full8_inj`, `full10_inj`, `full12_inj`; so are the five layouts of its sharp certificate: `ring12_inj`,
`ar12_inj`, `br12_inj`, `uni14_inj`, `biv14_inj`. Injectivity does not depend on the mask `vm` of the variables
of the columns (`layoutInj_congr`).
-/

@[expose] public section

namespace CAP.VR

open MvPolynomial Finset

theorem slot_zero_of_lt {w x m j : ℕ} (hx : x < 2 ^ (w * m)) (hj : m ≤ j) : slot w x j = 0 := by
  rw [slot_eq, Nat.div_eq_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left w hj))),
    Nat.zero_mod]

theorem bit31 : ∀ i : Fin 5, bitAt 31 i = 1 := by decide

/-- **Soundness of the test of a layout.** -/
theorem layoutOk_sound {L : Lay} {w slots : ℕ} (h : layoutOk L w slots = true) : LayoutInj L := by
  classical
  obtain ⟨L', hL'⟩ : ∃ L' : Lay, L' = Lay.mk L.k0 L.k1 L.k2 L.k3 L.k4 L.pv L.pm 31 L.D L.Dp := ⟨_, rfl⟩
  have hvm : L'.vm = 31 := by rw [hL']
  have hpm : L'.pm = L.pm := by rw [hL']
  have hpv : L'.pv = L.pv := by rw [hL']
  have hposL : ∀ e, pos L' e = pos L e := fun e => by
    rw [hL']
    rfl
  have h' : (Nat.ble 1 w && Nat.blt (maskAt 0 L' L.D L.Dp 0) (Nat.shiftLeft 1 w)
      && Nat.beq (Nat.shiftRight (maskAt w L' L.D L.Dp 0) (Nat.mul w slots)) 0
      && Nat.beq (Nat.land (maskAt w L' L.D L.Dp 0) (Nat.mul (ones w slots) (Nat.sub (Nat.shiftLeft 1 w) 2))) 0)
      = true := by
    rw [hL']
    exact h
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
  have hw : 1 ≤ w := Nat.le_of_ble_eq_true h1
  have hcnt : maskAt 0 L' L.D L.Dp 0 < 2 ^ w := by
    rw [Nat.blt_eq, show Nat.shiftLeft 1 w = 2 ^ w from Nat.one_shiftLeft w] at h2
    exact h2
  have hM : maskAt w L' L.D L.Dp 0 < 2 ^ (w * slots) := lt_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true h3)
  have hand : maskAt w L' L.D L.Dp 0 &&& ((2 ^ w - 2 ^ 1) * packSum w slots (fun _ => 1)) = 0 := by
    have h4' := Nat.eq_of_beq_eq_true h4
    rw [show Nat.shiftLeft 1 w = 2 ^ w from Nat.one_shiftLeft w] at h4'
    have h4'' : maskAt w L' L.D L.Dp 0 &&& (ones w slots * (2 ^ w - 2 ^ 1)) = 0 := h4'
    rw [ones_eq w slots hw, mul_comm] at h4''
    exact h4''
  set G := HP L' L.D L.Dp 0 with hG
  set S := G.support with hS
  set m := max slots (S.sup (pos L') + 1) with hm
  have hpos : ∀ e ∈ S, pos L' e < m := fun e he =>
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := pos L') he)) (le_max_right _ _)
  set κ : ℕ → ℕ := fun p => ∑ e ∈ S with pos L' e = p, coeff e G with hκ
  have hmono : maskAt w L' L.D L.Dp 0 = packSum w m κ := by
    rw [← evN_HP, evN_eq, ← sum_eq_packSum w L' m S (fun e => coeff e G) hpos]
  have hκlt : ∀ p, κ p < 2 ^ w := fun p => by
    refine lt_of_le_of_lt ?_ hcnt
    rw [← csum_HP, csum_eq]
    exact sum_le_sum_of_subset (filter_subset _ _)
  have hslot : ∀ p, p < m → κ p = slot w (maskAt w L' L.D L.Dp 0) p := fun p hp => by
    rw [hmono, slot_packSum w m κ (fun j _ => hκlt j) p hp]
  have hdig : ∀ p, slot w (maskAt w L' L.D L.Dp 0) p < 2 := fun p => by
    by_cases hp : p < slots
    · have hrep : packSum w slots (slot w (maskAt w L' L.D L.Dp 0)) = maskAt w L' L.D L.Dp 0 :=
        packSum_slot w slots _ hM
      have hd := slots_lt_of_and_hi w 1 slots (slot w (maskAt w L' L.D L.Dp 0)) hw (fun j _ => slot_lt _ _ _)
        (by rw [hrep]; exact hand) p hp
      simpa using hd
    · rw [slot_zero_of_lt hM (by omega)]
      norm_num
  have hmem : ∀ e, Adm L e → e ∈ S := fun e ha => by
    have hc := HP_full L' L.D L.Dp 0 e (fun i hi => absurd (by rw [hvm]; exact bit31 i) hi) ha.1
      (by rw [hpm]; exact ha.2.1) (by rw [hpv]; exact ha.2.2)
    rw [hS, mem_support_iff]
    exact Nat.one_le_iff_ne_zero.mp hc
  intro e e' he he' hpe
  by_contra hne
  have heS := hmem e he
  have he'S := hmem e' he'
  have hsub : ({e, e'} : Finset (Fin 5 →₀ ℕ)) ⊆ S.filter (fun x => pos L' x = pos L' e) := by
    intro x hx
    rw [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.mpr ⟨heS, rfl⟩
    · exact mem_filter.mpr ⟨he'S, by rw [hposL, hposL, hpe]⟩
  have hle := sum_le_sum_of_subset (f := fun x => coeff x G) hsub
  rw [sum_pair hne] at hle
  have c1 : coeff e G ≠ 0 := mem_support_iff.mp heS
  have c2 : coeff e' G ≠ 0 := mem_support_iff.mp he'S
  have hk2 : 2 ≤ κ (pos L' e) := by
    show 2 ≤ ∑ x ∈ S with pos L' x = pos L' e, coeff x G
    omega
  have hd := hdig (pos L' e)
  rw [← hslot _ (hpos e heS)] at hd
  omega

/-- Injectivity depends on the strides, the parity vectors, the mask of the pair variables and the two bounds. -/
theorem layoutInj_congr {L L' : Lay} (h : LayoutInj L)
    (e : (L'.k0, L'.k1, L'.k2, L'.k3, L'.k4, L'.pv, L'.pm, L'.D, L'.Dp)
      = (L.k0, L.k1, L.k2, L.k3, L.k4, L.pv, L.pm, L.D, L.Dp)) : LayoutInj L' := by
  obtain ⟨a0, a1, a2, a3, a4, apv, apm, avm, aD, aDp⟩ := L
  obtain ⟨b0, b1, b2, b3, b4, bpv, bpm, bvm, bD, bDp⟩ := L'
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
  exact h

/-! ## The layouts of the certificates of T8 -/

/-- The layout of a ring type: two ring points and their inner product, degree 10, with the classes of the two
sign changes. -/
theorem ring10_inj : LayoutInj ⟨12, 51, 257, 896, 2, 153, 0, 31, 10, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 8961) (by decide +kernel)

/-- The layout of a record type A r: degree 10, pair degree 4 in the variables of the pair point and the deviation. -/
theorem ar10_inj : LayoutInj ⟨22, 94, 2, 318, 65, 68, 19, 31, 10, 4⟩ :=
  layoutOk_sound (w := 16) (slots := 3181) (by decide +kernel)

/-- The layout of a record type B r. -/
theorem br10_inj : LayoutInj ⟨22, 94, 318, 2, 65, 20, 19, 31, 10, 4⟩ :=
  layoutOk_sound (w := 16) (slots := 3181) (by decide +kernel)

/-- The layout of all monomials of degree at most 8. -/
theorem full8_inj : LayoutInj ⟨1, 14, 76, 431, 1563, 0, 0, 31, 8, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 12505) (by decide +kernel)

/-- The layout of all monomials of degree at most 10. -/
theorem full10_inj : LayoutInj ⟨1, 14, 141, 655, 3575, 0, 0, 31, 10, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 35751) (by decide +kernel)

/-- The layout of all monomials of degree at most 12. -/
theorem full12_inj : LayoutInj ⟨1, 15, 153, 1017, 7750, 0, 0, 31, 12, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 93001) (by decide +kernel)

/-! ## The layouts of the sharp certificate of T8 (degree 12) -/

/-- The layout of the record of two ring points of the degree 12. -/
theorem ring12_inj : LayoutInj ⟨7, 283, 67, 1749, 3, 153, 0, 31, 12, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 20989) (by decide +kernel)

/-- The layout of the record A r of the degree 12, pair degree 4. -/
theorem ar12_inj : LayoutInj ⟨13, 97, 3, 351, 59, 68, 19, 31, 12, 4⟩ :=
  layoutOk_sound (w := 16) (slots := 4213) (by decide +kernel)

/-- The layout of the record B r of the degree 12, pair degree 4. -/
theorem br12_inj : LayoutInj ⟨13, 97, 351, 3, 59, 20, 19, 31, 12, 4⟩ :=
  layoutOk_sound (w := 16) (slots := 4213) (by decide +kernel)

/-- The layout of the polynomials of the degree 14 in the first variable: the other variables are pair variables,
and the pair degree is zero. -/
theorem uni14_inj : LayoutInj ⟨1, 0, 0, 0, 0, 0, 30, 31, 14, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 15) (by decide +kernel)

/-- The layout of the polynomials of the degree 14 in the first two variables. -/
theorem biv14_inj : LayoutInj ⟨1, 15, 0, 0, 0, 0, 28, 31, 14, 0⟩ :=
  layoutOk_sound (w := 16) (slots := 211) (by decide +kernel)

end CAP.VR
