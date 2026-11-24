module

public import CAP.VR.Label

/-!
# Virtual-root certificates: the theorem of the schema S4, in coordinates

`energy_coords`: if the labels are checked (`labelsOk`), every record type has a checked record identity and a
checked minorant identity, every label a checked identity (`Checked`), and the bound is checked (`boundOk`),
then every configuration of the piece (`InPiece`) has an energy above `Bn / Bd`.

The proof is the one of the source (`prop:VRsound`): the energy of a pair is at least its minorant minus the
loss of the minorant; the minorant is the record plus the record constant, twice the kernel and the two
exchange values; the record is at least minus its loss (`pair_ineq`); the exchange values of a label add up to
at least the kernel on the diagonal plus the guard term minus the loss of the label (`label_ineq`); and the
kernel is positive semidefinite (`Kl_psd`).
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open Finset

variable {P : Par} {heads : List RecH} {C : Conf}

/-! ## Sums -/

theorem sumN_eq (f : ℕ → ℕ) : ∀ n, sumN f n = ∑ k ∈ range n, f k
  | 0 => rfl
  | n + 1 => by
    rw [Finset.sum_range_succ, ← sumN_eq f n]
    rfl

/-- The sum over the pairs `i < j` of `a i j + a j i` is the sum over the ordered pairs of distinct indices. -/
theorem sum_pairs (a : ℕ → ℕ → ℝ) : ∀ n : ℕ,
    ∑ j ∈ range n, ∑ i ∈ range j, (a i j + a j i) = ∑ l ∈ range n, ∑ o ∈ range n, if o = l then 0 else a l o
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_pairs a n,
      Finset.sum_range_succ (fun l => ∑ o ∈ range (n + 1), if o = l then 0 else a l o) n]
    have e1 : ∀ l ∈ range n, (∑ o ∈ range (n + 1), if o = l then 0 else a l o)
        = (∑ o ∈ range n, if o = l then 0 else a l o) + a l n := by
      intro l hl
      have hl' := Finset.mem_range.1 hl
      rw [Finset.sum_range_succ, if_neg (by omega)]
    have e2 : (∑ o ∈ range (n + 1), if o = n then 0 else a n o) = ∑ o ∈ range n, a n o := by
      rw [Finset.sum_range_succ, if_pos rfl, add_zero]
      refine Finset.sum_congr rfl fun o ho => ?_
      have ho' := Finset.mem_range.1 ho
      rw [if_neg (by omega)]
    rw [Finset.sum_congr rfl e1, e2]
    simp only [Finset.sum_add_distrib]
    ring

theorem sum_ne (f : ℕ → ℝ) {n l : ℕ} (hl : l < n) :
    ∑ o ∈ range n, (if o = l then 0 else f o) = ∑ o ∈ range n, f o - f l := by
  have h : ∑ o ∈ range n, f o = ∑ o ∈ range n, ((if o = l then 0 else f o) + (if o = l then f o else 0)) := by
    refine Finset.sum_congr rfl fun o _ => ?_
    split_ifs <;> simp
  rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq' (range n) l f, if_pos (Finset.mem_range.2 hl)]
  ring

theorem pow_sub_real {e F : ℕ} (h : e ≤ F) (a : ℝ) : a * 2 ^ (F - e) = 2 ^ F * (a / 2 ^ e) := by
  rw [pow_sub₀ (2 : ℝ) two_ne_zero h]
  field_simp

/-! ## The check of the bound -/

theorem nthLoss_tl (rl : List Loss) (k : ℕ) : nthLoss (gmOk.tlL rl) k = nthLoss rl (k + 1) := by
  cases rl <;> rfl

theorem nth_tl (g : List ℕ) (k : ℕ) : nth (tl g) k = nth g (k + 1) := by
  cases g <;> rfl

theorem hd_nth (g : List ℕ) : hd g = nth g 0 := by
  cases g <;> rfl

theorem gmOk_nth {F : ℕ} : ∀ (heads : List RecH) (rl ml : List Loss) (gm : List ℕ),
    gmOk P F heads rl ml gm = true → ∀ k, k < lenH heads →
      (nthLoss rl k).E ≤ F ∧ P.sP ≤ F
        ∧ (nthLoss ml k).rho * (nthH heads k).hid * 2 ^ F
          ≤ nth gm k * ((nthH heads k).hid + (nthH heads k).hin - (nthH heads k).hip) * 2 ^ ((nthLoss ml k).E + 1)
  | [], _, _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | h :: hs, rl, ml, gm, hok, k, hk => by
    have h' : (Nat.ble (nthLoss rl 0).E F && Nat.ble P.sP F && Nat.blt h.hip (Nat.add h.hid h.hin)
        && Nat.ble (Nat.shiftLeft (Nat.mul (nthLoss ml 0).rho h.hid) F)
            (Nat.shiftLeft (Nat.mul (hd gm) (Nat.sub (Nat.add h.hid h.hin) h.hip)) (Nat.succ (nthLoss ml 0).E))
        && gmOk P F hs (gmOk.tlL rl) (gmOk.tlL ml) (tl gm)) = true := hok
    simp only [Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨a, b⟩, _⟩, d⟩, e⟩ := h'
    cases k with
    | zero =>
      refine ⟨Nat.le_of_ble_eq_true a, Nat.le_of_ble_eq_true b, ?_⟩
      have hd' := Nat.le_of_ble_eq_true d
      rw [show Nat.shiftLeft (Nat.mul (nthLoss ml 0).rho h.hid) F = (nthLoss ml 0).rho * h.hid * 2 ^ F from
          Nat.shiftLeft_eq _ _,
        show Nat.shiftLeft (Nat.mul (hd gm) (Nat.sub (Nat.add h.hid h.hin) h.hip)) (Nat.succ (nthLoss ml 0).E)
          = hd gm * (h.hid + h.hin - h.hip) * 2 ^ ((nthLoss ml 0).E + 1) from Nat.shiftLeft_eq _ _, hd_nth] at hd'
      exact hd'
    | succ k =>
      have ih := gmOk_nth hs (gmOk.tlL rl) (gmOk.tlL ml) (tl gm) e k (Nat.lt_of_succ_lt_succ hk)
      rw [nthLoss_tl, nthLoss_tl, nth_tl] at ih
      exact ih

/-- The loss of a pair of labels, in the unit `2 ^ -F`. -/
noncomputable def pairLoss (P : Par) (heads : List RecH) (rl : List Loss) (gm : List ℕ) (F i j : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.shiftLeft (nthH heads (nth P.rt (pairIndex i j))).cn (Nat.sub F P.sP))
    (Nat.shiftLeft (nthLoss rl (nth P.rt (pairIndex i j))).rho (Nat.sub F (nthLoss rl (nth P.rt (pairIndex i j))).E)))
    (nth gm (nth P.rt (pairIndex i j)))

noncomputable def pairGain (P : Par) (heads : List RecH) (F i j : ℕ) : ℕ :=
  Nat.shiftLeft (nthH heads (nth P.rt (pairIndex i j))).cp (Nat.sub F P.sP)

noncomputable def labLoss (cl : List Loss) (F l : ℕ) : ℕ := Nat.shiftLeft (nthLoss cl l).rho (Nat.sub F (nthLoss cl l).E)

noncomputable def labGain (P : Par) (F l : ℕ) : ℕ :=
  cond (Nat.ble 2 (nth P.dcls l))
    (Nat.shiftLeft (Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2)))
      (Nat.sub F P.sP)) 0

theorem pairLoss_real (P : Par) (heads : List RecH) (rl : List Loss) (gm : List ℕ) (F i j : ℕ) :
    (pairLoss P heads rl gm F i j : ℝ)
      = ((nthH heads (nth P.rt (pairIndex i j))).cn : ℝ) * 2 ^ (F - P.sP)
        + ((nthLoss rl (nth P.rt (pairIndex i j))).rho : ℝ) * 2 ^ (F - (nthLoss rl (nth P.rt (pairIndex i j))).E)
        + (nth gm (nth P.rt (pairIndex i j)) : ℝ) := by
  show (((Nat.shiftLeft (nthH heads (nth P.rt (pairIndex i j))).cn (F - P.sP)
    + Nat.shiftLeft (nthLoss rl (nth P.rt (pairIndex i j))).rho (F - (nthLoss rl (nth P.rt (pairIndex i j))).E)
    + nth gm (nth P.rt (pairIndex i j)) : ℕ)) : ℝ) = _
  rw [Nat.cast_add, Nat.cast_add, cast_shl, cast_shl]

theorem pairGain_real (P : Par) (heads : List RecH) (F i j : ℕ) :
    (pairGain P heads F i j : ℝ) = ((nthH heads (nth P.rt (pairIndex i j))).cp : ℝ) * 2 ^ (F - P.sP) := by
  show ((Nat.shiftLeft (nthH heads (nth P.rt (pairIndex i j))).cp (F - P.sP) : ℕ) : ℝ) = _
  rw [cast_shl]

theorem labLoss_real (cl : List Loss) (F l : ℕ) :
    (labLoss cl F l : ℝ) = ((nthLoss cl l).rho : ℝ) * 2 ^ (F - (nthLoss cl l).E) := by
  show ((Nat.shiftLeft (nthLoss cl l).rho (F - (nthLoss cl l).E) : ℕ) : ℝ) = _
  rw [cast_shl]

theorem labGain_real (P : Par) (F l : ℕ) : (labGain P F l : ℝ) = (guardN P l : ℝ) * 2 ^ (F - P.sP) := by
  unfold labGain guardN
  cases Nat.ble 2 (nth P.dcls l)
  · show ((0 : ℕ) : ℝ) = ((0 : ℕ) : ℝ) * _
    simp
  · show ((Nat.shiftLeft (Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2)))
      (F - P.sP) : ℕ) : ℝ) = _
    rw [cast_shl]
    rfl

/-- The content of the check `boundOk`. -/
theorem boundOk_real {rl ml cl : List Loss} {gm : List ℕ} {F Bn Bd : ℕ}
    (hb : boundOk P heads rl ml cl gm F Bn Bd = true) :
    gmOk P F heads rl ml gm = true ∧ (∀ l, l < 9 → (nthLoss cl l).E ≤ F)
      ∧ (Bn : ℝ) * 2 ^ F
          + Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, (pairLoss P heads rl gm F i j : ℝ)) + ∑ l ∈ range 9, (labLoss cl F l : ℝ))
        < Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, (pairGain P heads F i j : ℝ)) + ∑ l ∈ range 9, (labGain P F l : ℝ)) := by
  have hb' : (gmOk P F heads rl ml gm && allN (fun l => Nat.ble (nthLoss cl l).E F) 9
      && Nat.blt
        (Nat.add (Nat.shiftLeft Bn F)
          (Nat.mul Bd (Nat.add (sumN (fun j => sumN (fun i => pairLoss P heads rl gm F i j) j) 9) (sumN (labLoss cl F) 9))))
        (Nat.mul Bd (Nat.add (sumN (fun j => sumN (fun i => pairGain P heads F i j) j) 9) (sumN (labGain P F) 9))))
      = true := hb
  simp only [Bool.and_eq_true] at hb'
  obtain ⟨⟨hgm, hE⟩, hlt⟩ := hb'
  refine ⟨hgm, fun l hl => Nat.le_of_ble_eq_true (allN_lt 9 hE l hl), ?_⟩
  have e1 : sumN (fun j => sumN (fun i => pairLoss P heads rl gm F i j) j) 9
      = ∑ j ∈ range 9, ∑ i ∈ range j, pairLoss P heads rl gm F i j := by
    rw [sumN_eq]
    exact Finset.sum_congr rfl fun j _ => sumN_eq _ _
  have e2 : sumN (fun j => sumN (fun i => pairGain P heads F i j) j) 9
      = ∑ j ∈ range 9, ∑ i ∈ range j, pairGain P heads F i j := by
    rw [sumN_eq]
    exact Finset.sum_congr rfl fun j _ => sumN_eq _ _
  have h0 : Bn * 2 ^ F + Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, pairLoss P heads rl gm F i j) + ∑ l ∈ range 9, labLoss cl F l)
      < Bd * ((∑ j ∈ range 9, ∑ i ∈ range j, pairGain P heads F i j) + ∑ l ∈ range 9, labGain P F l) := by
    have h := lt_of_blt hlt
    rw [e1, e2, sumN_eq, sumN_eq, show Nat.shiftLeft Bn F = Bn * 2 ^ F from Nat.shiftLeft_eq _ _] at h
    exact h
  have hR := (Nat.cast_lt (α := ℝ)).2 h0
  push_cast at hR
  exact hR

/-! ## The theorem of the schema -/

/-- **The checked identities of a virtual-root certificate**: every record type has a checked record identity and a
checked minorant identity, and every label has a checked identity, with the scales and the norms of the residuals
that the lists `rl`, `ml`, `cl` record, in layouts that are injective on the admissible monomials. -/
structure Checked (P : Par) (heads : List RecH) (rl ml cl : List Loss) : Prop where
  recs : ∀ k, k < lenH heads → ∃ x : RecX, LayoutInj x.L ∧ recordOk P (nthH heads k) x = true
    ∧ x.E = (nthLoss rl k).E ∧ x.rho = (nthLoss rl k).rho
  minos : ∀ k, k < lenH heads → ∃ x : MinoX, LayoutInj x.L ∧ minoOk P (nthH heads k) x = true
    ∧ x.E = (nthLoss ml k).E ∧ x.rho = (nthLoss ml k).rho
  clss : ∀ l, l < 9 → ∃ x : ClsX, LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l
    ∧ x.E = (nthLoss cl l).E ∧ x.rho = (nthLoss cl l).rho

/-- **The theorem of the schema S4, in coordinates.** A configuration of the piece of a checked virtual-root
certificate has an energy above the bound `Bn / Bd` of the certificate. -/
theorem energy_coords {rl ml cl : List Loss} {gm : List ℕ} {F Bn Bd : ℕ} (hlab : labelsOk P heads = true)
    (hck : Checked P heads rl ml cl) (hb : boundOk P heads rl ml cl gm F Bn Bd = true) (hin : InPiece P heads C) :
    (Bn : ℝ) / Bd < ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) := by
  have lab := labOk_of hlab
  obtain ⟨hgm, hclE, hR⟩ := boundOk_real hb
  have hkx : ∀ i j, i < j → j < 9 → nth P.rt (pairIndex i j) < lenH heads := fun i j hij hj => by
    have hp := lab.pair i j hij hj
    unfold pairOk at hp
    rw [Bool.and_eq_true] at hp
    exact lt_of_blt hp.1
  have hsP : P.sP ≤ F := (gmOk_nth heads rl ml gm hgm _ (hkx 0 1 (by norm_num) (by norm_num))).2.1
  -- the pairs
  have hpair : ∀ j ∈ range 9, ∀ i ∈ range j,
      ((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F + 2 * Kl P C i j
        + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP ≤ 1 / (2 - 2 * C.t i j) := by
    intro j hj i hi
    rw [Finset.mem_range] at hj hi
    obtain ⟨y, σu, σv, m0, m1, Fa⟩ := rec_facts hlab hin hi hj
    obtain ⟨x, hxL, hxok, hxE, hxr⟩ := hck.recs _ (hkx i j hi hj)
    obtain ⟨mx, hmL, hmok, hmE, hmr⟩ := hck.minos _ (hkx i j hi hj)
    have h1 := pair_ineq Fa hxL hxok hmL hmok
    obtain ⟨hEk, _, hg⟩ := gmOk_nth heads rl ml gm hgm _ (hkx i j hi hj)
    rw [hxE, hxr, hmE, hmr] at h1
    -- the loss of the minorant
    have hgp : (0 : ℝ) < ((hdOf P heads i j).hid : ℝ) + (hdOf P heads i j).hin - (hdOf P heads i j).hip := by
      have : ((hdOf P heads i j).hip : ℝ) < ((hdOf P heads i j).hid : ℝ) + (hdOf P heads i j).hin := by
        exact_mod_cast Fa.hi1
      linarith
    have e : ((((hdOf P heads i j).hid + (hdOf P heads i j).hin - (hdOf P heads i j).hip : ℕ)) : ℝ)
        = ((hdOf P heads i j).hid : ℝ) + (hdOf P heads i j).hin - (hdOf P heads i j).hip := by
      rw [Nat.cast_sub (le_of_lt Fa.hi1), Nat.cast_add]
    have hg' : (((nthLoss ml (nth P.rt (pairIndex i j))).rho * (hdOf P heads i j).hid * 2 ^ F : ℕ) : ℝ)
        ≤ ((nth gm (nth P.rt (pairIndex i j))
          * ((hdOf P heads i j).hid + (hdOf P heads i j).hin - (hdOf P heads i j).hip)
          * 2 ^ ((nthLoss ml (nth P.rt (pairIndex i j))).E + 1) : ℕ) : ℝ) := by exact_mod_cast hg
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, e, Nat.cast_pow, Nat.cast_pow] at hg'
    have hml : ((nthLoss ml (nth P.rt (pairIndex i j))).rho * (hdOf P heads i j).hid : ℝ)
          / (2 ^ ((nthLoss ml (nth P.rt (pairIndex i j))).E + 1)
            * (((hdOf P heads i j).hid : ℝ) + (hdOf P heads i j).hin - (hdOf P heads i j).hip))
        ≤ (nth gm (nth P.rt (pairIndex i j)) : ℝ) / 2 ^ F := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [h2] at hg'
      linarith
    have hval : ((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F
        = (((hdOf P heads i j).cp : ℝ) - (hdOf P heads i j).cn) / 2 ^ P.sP
          - (nthLoss rl (nth P.rt (pairIndex i j))).rho / 2 ^ (nthLoss rl (nth P.rt (pairIndex i j))).E
          - (nth gm (nth P.rt (pairIndex i j)) : ℝ) / 2 ^ F := by
      rw [pairGain_real, pairLoss_real, pow_sub_real hsP, pow_sub_real hsP, pow_sub_real hEk]
      have hF : (2 : ℝ) ^ F ≠ 0 := by positivity
      show (2 ^ F * (((hdOf P heads i j).cp : ℝ) / 2 ^ P.sP)
        - (2 ^ F * (((hdOf P heads i j).cn : ℝ) / 2 ^ P.sP)
          + 2 ^ F * (((nthLoss rl (nth P.rt (pairIndex i j))).rho : ℝ) / 2 ^ (nthLoss rl (nth P.rt (pairIndex i j))).E)
          + (nth gm (nth P.rt (pairIndex i j)) : ℝ))) / 2 ^ F = _
      field_simp
      ring
    rw [hval]
    linarith
  -- the labels
  have hlabel : ∀ l ∈ range 9,
      Kl P C l l + ((labGain P F l : ℝ) - labLoss cl F l) / 2 ^ F
        ≤ (∑ o ∈ range 9, if o = l then 0 else piN P heads C l o) / 2 ^ P.sP := by
    intro l hl
    rw [Finset.mem_range] at hl
    obtain ⟨x, hxL, hxok, rfl, hxE, hxr⟩ := hck.clss l hl
    have h1 := label_ineq hlab hin hxL hxok
    rw [hxE, hxr] at h1
    have hval : ((labGain P F x.label : ℝ) - labLoss cl F x.label) / 2 ^ F
        = (guardN P x.label : ℝ) / 2 ^ P.sP - (nthLoss cl x.label).rho / 2 ^ (nthLoss cl x.label).E := by
      rw [labGain_real, labLoss_real, pow_sub_real hsP, pow_sub_real (hclE x.label hl)]
      have hF : (2 : ℝ) ^ F ≠ 0 := by positivity
      field_simp
    rw [hval]
    linarith
  -- the sum over the pairs
  have h1 := Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hpair j hj i hi
  have h2 : ∑ j ∈ range 9, ∑ i ∈ range j, (((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F
        + 2 * Kl P C i j + (piN P heads C i j + piN P heads C j i) / 2 ^ P.sP)
      = (∑ j ∈ range 9, ∑ i ∈ range j, ((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F)
        + (∑ j ∈ range 9, ∑ i ∈ range j, (Kl P C i j + Kl P C j i))
        + (∑ j ∈ range 9, ∑ i ∈ range j, (piN P heads C i j + piN P heads C j i)) / 2 ^ P.sP := by
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Kl_comm P C j i]
    ring
  have e1 := sum_pairs (fun i j => Kl P C i j) 9
  have e2 := sum_pairs (fun i j => piN P heads C i j) 9
  rw [h2, e1, e2] at h1
  have h3 : ∑ l ∈ range 9, (∑ o ∈ range 9, if o = l then 0 else Kl P C l o)
      = ∑ l ∈ range 9, ∑ o ∈ range 9, Kl P C l o - ∑ l ∈ range 9, Kl P C l l := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l hl => sum_ne _ (Finset.mem_range.1 hl)
  have h5 : ∑ l ∈ range 9, (Kl P C l l + ((labGain P F l : ℝ) - labLoss cl F l) / 2 ^ F)
      ≤ (∑ l ∈ range 9, ∑ o ∈ range 9, if o = l then 0 else piN P heads C l o) / 2 ^ P.sP := by
    rw [Finset.sum_div]
    exact Finset.sum_le_sum hlabel
  rw [Finset.sum_add_distrib] at h5
  have h6 := Kl_psd P C (range 9)
  rw [h3] at h1
  -- the energy is at least the sum of the gains minus the sum of the losses
  have hsum : (∑ j ∈ range 9, ∑ i ∈ range j, ((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F)
      + ∑ l ∈ range 9, ((labGain P F l : ℝ) - labLoss cl F l) / 2 ^ F
      ≤ ∑ j ∈ range 9, ∑ i ∈ range j, 1 / (2 - 2 * C.t i j) := by linarith
  -- the bound
  have hF : (0 : ℝ) < 2 ^ F := by positivity
  have hBd : (0 : ℝ) < Bd := by
    rcases Nat.eq_zero_or_pos Bd with h0 | h0
    · rw [h0] at hR
      simp only [Nat.cast_zero, zero_mul, add_zero] at hR
      have : (0 : ℝ) ≤ (Bn : ℝ) * 2 ^ F := by positivity
      linarith
    · exact_mod_cast h0
  have hS : (∑ j ∈ range 9, ∑ i ∈ range j, ((pairGain P heads F i j : ℝ) - pairLoss P heads rl gm F i j) / 2 ^ F)
      + ∑ l ∈ range 9, ((labGain P F l : ℝ) - labLoss cl F l) / 2 ^ F
      = (((∑ j ∈ range 9, ∑ i ∈ range j, (pairGain P heads F i j : ℝ)) + ∑ l ∈ range 9, (labGain P F l : ℝ))
        - ((∑ j ∈ range 9, ∑ i ∈ range j, (pairLoss P heads rl gm F i j : ℝ)) + ∑ l ∈ range 9, (labLoss cl F l : ℝ)))
        / 2 ^ F := by
    simp only [← Finset.sum_div, Finset.sum_sub_distrib]
    ring
  rw [hS] at hsum
  refine lt_of_lt_of_le ?_ hsum
  rw [div_lt_div_iff₀ hBd hF]
  nlinarith

end CAP.VR
