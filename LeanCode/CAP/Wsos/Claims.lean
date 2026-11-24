module

public import CAP.Wsos.Energy
public import CAP.Wsos.Support

/-!
# The declared domain of a typed certificate contains a claim

A claim of the source consists of a class structure and of an interval `K a b` for every pair type; all
intervals lie below the separation bound `T < 1`. A labelled configuration satisfies the claim if the
inner product of every pair of distinct points lies in the interval of its pair type (`InClaim`).

`inSource_of_claim`: if the check `claimOk` succeeds, then every configuration that satisfies the claim
lies in the domain that the certificate declares (`InSource`). So the theorem of a certificate holds for
the configurations of the claim, without hypotheses on the further inequalities of the domain
(`energy_gt_claim`). This is the step from the conditions (D1) and (D2) of the source to its soundness
theorem for a claim. The proof:

* a point of a class of a one-edge type has a partner (`Labelling.partner`), and the inner product with
  the partner is at most the upper end of the interval of the one-edge type (`claim_partner`);
* all inner products of distinct points are at most `T` (`claim_le_T`); in particular the points are
  distinct;
* (D1) the lower end of an interval of the domain is at most that of the claim, or it is a cap bound
  through a partner, by `cap_witness` with the rational witness of the check (`claim_iv`);
* (D2) every cut of the domain is a support polynomial whose root has a partner outside the triple, and
  it is nonnegative by `support_witness` with the rational witness of the check (`claim_cuts`).
-/

@[expose] public section

namespace CAP.Wsos

open Finset CAP.ThreePoint

/-! ## The comparisons of the check -/

theorem hiLe_sound {I : Ival} {tp tq : ℕ} (hhd : 0 < I.hd) (htq : 0 < tq) (h : hiLe I tp tq = true) :
    I.hi ≤ (tp : ℝ) / tq := by
  have h' : I.hp * tq ≤ I.hn * tq + tp * I.hd := Nat.le_of_ble_eq_true h
  have hR : (I.hp : ℝ) * tq ≤ I.hn * tq + tp * I.hd := by exact_mod_cast h'
  have h1 : (0 : ℝ) < I.hd := Nat.cast_pos.mpr hhd
  have h2 : (0 : ℝ) < tq := Nat.cast_pos.mpr htq
  unfold Ival.hi
  rw [div_le_div_iff₀ h1 h2]
  linarith

theorem hiLeHi_sound {K J : Ival} (hK : 0 < K.hd) (hJ : 0 < J.hd) (h : hiLeHi K J = true) : K.hi ≤ J.hi := by
  have h' : K.hp * J.hd + J.hn * K.hd ≤ J.hp * K.hd + K.hn * J.hd := Nat.le_of_ble_eq_true h
  have hR : (K.hp : ℝ) * J.hd + J.hn * K.hd ≤ J.hp * K.hd + K.hn * J.hd := by exact_mod_cast h'
  have h1 : (0 : ℝ) < K.hd := Nat.cast_pos.mpr hK
  have h2 : (0 : ℝ) < J.hd := Nat.cast_pos.mpr hJ
  unfold Ival.hi
  rw [div_le_div_iff₀ h1 h2]
  linarith

theorem loLeLo_sound {J K : Ival} (hJ : 0 < J.ld) (hK : 0 < K.ld) (h : loLeLo J K = true) : J.lo ≤ K.lo := by
  have h' : J.lp * K.ld + K.ln * J.ld ≤ K.lp * J.ld + J.ln * K.ld := Nat.le_of_ble_eq_true h
  have hR : (J.lp : ℝ) * K.ld + K.ln * J.ld ≤ K.lp * J.ld + J.ln * K.ld := by exact_mod_cast h'
  have h1 : (0 : ℝ) < J.ld := Nat.cast_pos.mpr hJ
  have h2 : (0 : ℝ) < K.ld := Nat.cast_pos.mpr hK
  unfold Ival.lo
  rw [div_le_div_iff₀ h1 h2]
  linarith

/-- The check of a cap bound gives the hypotheses of `cap_witness`: the number `m` and the lower end of
the interval `J` in the form `-(a T) - m`, for the cap `c = -(hi Kw)`. -/
theorem capIneq_sound {J Kw : Ival} {lp lq tp tq : ℕ} (hJ : 0 < J.ld) (hlq : 0 < lq) (htq : 0 < tq)
    (hK : 0 < Kw.hd) (h : capIneq J Kw lp lq tp tq = true) :
    ∃ m : ℝ, 0 ≤ m ∧ 1 + ((lp : ℝ) / lq) ^ 2 - 2 * ((lp : ℝ) / lq) * (-Kw.hi) ≤ m ^ 2
      ∧ J.lo = -((lp : ℝ) / lq * ((tp : ℝ) / tq)) - m := by
  unfold capIneq at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : J.lp * lq * tq + lp * tp * J.ld ≤ J.ln * lq * tq := Nat.le_of_ble_eq_true h1
  obtain ⟨Mn, hMn⟩ : ∃ Mn : ℕ, Mn = J.ln * lq * tq - (J.lp * lq * tq + lp * tp * J.ld) := ⟨_, rfl⟩
  have h2' : (lq * lq * Kw.hd + lp * lp * Kw.hd + 2 * (lp * lq) * Kw.hp) * (J.ld * J.ld * (tq * tq))
      ≤ Mn * Mn * Kw.hd + 2 * (lp * lq) * Kw.hn * (J.ld * J.ld * (tq * tq)) := by
    rw [hMn]
    exact Nat.le_of_ble_eq_true h2
  have h1R : (J.lp : ℝ) * lq * tq + lp * tp * J.ld ≤ J.ln * lq * tq := by exact_mod_cast h1'
  have hMR : (Mn : ℝ) = (J.ln : ℝ) * lq * tq - (J.lp * lq * tq + lp * tp * J.ld) := by
    rw [hMn, Nat.cast_sub h1']
    push_cast
    ring
  have h2R : ((lq : ℝ) * lq * Kw.hd + lp * lp * Kw.hd + 2 * (lp * lq) * Kw.hp) * (J.ld * J.ld * (tq * tq))
      ≤ (Mn : ℝ) * Mn * Kw.hd + 2 * (lp * lq) * Kw.hn * (J.ld * J.ld * (tq * tq)) := by exact_mod_cast h2'
  rw [hMR] at h2R
  have a1 : 0 ≤ -((J.lp : ℝ) - J.ln) * lq * tq - lp * tp * J.ld := by linarith
  have a2 : ((lq : ℝ) ^ 2 * Kw.hd + (lp : ℝ) ^ 2 * Kw.hd - 2 * lp * lq * ((Kw.hn : ℝ) - Kw.hp))
        * ((J.ld : ℝ) ^ 2 * (tq : ℝ) ^ 2)
      ≤ (-((J.lp : ℝ) - J.ln) * lq * tq - lp * tp * J.ld) ^ 2 * Kw.hd := by linarith
  obtain ⟨m, hm0, hm1, hm2⟩ := cap_arith (jl := (J.lp : ℝ) - J.ln) (jd := (J.ld : ℝ)) (lp := (lp : ℝ))
    (lq := (lq : ℝ)) (tp := (tp : ℝ)) (tq := (tq : ℝ)) (hc := (Kw.hn : ℝ) - Kw.hp) (hd := (Kw.hd : ℝ))
    (Nat.cast_pos.mpr hJ) (Nat.cast_pos.mpr hlq) (Nat.cast_pos.mpr htq) (Nat.cast_pos.mpr hK) a1 a2
  have e : -Kw.hi = ((Kw.hn : ℝ) - Kw.hp) / Kw.hd := by
    unfold Ival.hi
    ring
  refine ⟨m, hm0, ?_, ?_⟩
  · rw [e]
    exact hm1
  · unfold Ival.lo
    exact hm2

/-- The check of the constant of a support cut gives the bound of the support inequality, for the cap
`c = -(hi Kw)`. -/
theorem supIneq_sound {Kw : Ival} {w : SupW} {tp tq : ℕ} (hk : 0 < w.kap) (hB : 0 < w.B) (haq : 0 < w.aq)
    (htq : 0 < tq) (hK : 0 < Kw.hd) (h : supIneq Kw w tp tq = true) :
    (w.B : ℝ) / w.kap + 2 * ((w.ap : ℝ) / w.aq) * ((tp : ℝ) / tq)
        + (1 + ((w.ap : ℝ) / w.aq) ^ 2 - 2 * ((w.ap : ℝ) / w.aq) * (-Kw.hi)) / (2 * ((w.B : ℝ) / w.kap))
      ≤ (w.G : ℝ) / w.kap := by
  have h' : 2 * (w.B * w.B) * (w.aq * w.aq) * tq * Kw.hd + w.kap * w.kap * (w.aq * w.aq + w.ap * w.ap) * tq * Kw.hd
        + 4 * w.ap * w.aq * w.B * tp * w.kap * Kw.hd + 2 * (w.kap * w.kap) * (w.ap * w.aq) * Kw.hp * tq
      ≤ 2 * (w.B * w.G) * (w.aq * w.aq) * tq * Kw.hd + 2 * (w.kap * w.kap) * (w.ap * w.aq) * Kw.hn * tq :=
    Nat.le_of_ble_eq_true h
  have hR : 2 * ((w.B : ℝ) * w.B) * (w.aq * w.aq) * tq * Kw.hd
        + (w.kap : ℝ) * w.kap * (w.aq * w.aq + w.ap * w.ap) * tq * Kw.hd
        + 4 * (w.ap : ℝ) * w.aq * w.B * tp * w.kap * Kw.hd + 2 * ((w.kap : ℝ) * w.kap) * (w.ap * w.aq) * Kw.hp * tq
      ≤ 2 * ((w.B : ℝ) * w.G) * (w.aq * w.aq) * tq * Kw.hd + 2 * ((w.kap : ℝ) * w.kap) * (w.ap * w.aq) * Kw.hn * tq := by
    exact_mod_cast h'
  have e : -Kw.hi = ((Kw.hn : ℝ) - Kw.hp) / Kw.hd := by
    unfold Ival.hi
    ring
  rw [e]
  refine sup_arith (k := (w.kap : ℝ)) (B := (w.B : ℝ)) (G := (w.G : ℝ)) (ap := (w.ap : ℝ)) (aq := (w.aq : ℝ))
    (tp := (tp : ℝ)) (tq := (tq : ℝ)) (hc := (Kw.hn : ℝ) - Kw.hp) (hd := (Kw.hd : ℝ))
    (Nat.cast_pos.mpr hk) (Nat.cast_pos.mpr hB) (Nat.cast_pos.mpr haq) (Nat.cast_pos.mpr htq) (Nat.cast_pos.mpr hK) ?_
  linarith

/-! ## One-edge types and partners -/

theorem oneEdge_spec {q : ℕ} {C : Cert} {w1 w2 : ℕ} (h : oneEdge q C w1 w2 = true) :
    w2 < q ∧ ((w1 = w2 ∧ C.n w1 = 2) ∨ (w1 < w2 ∧ C.n w1 = 1 ∧ C.n w2 = 1)) := by
  unfold oneEdge at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at h
  obtain ⟨hq, h | h⟩ := h
  · exact ⟨hq, Or.inl ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2⟩⟩
  · exact ⟨hq, Or.inr ⟨h.1.1, Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩⟩

theorem inEdge_spec {w1 w2 a : ℕ} (h : inEdge w1 w2 a = true) : a = w1 ∨ a = w2 := by
  unfold inEdge at h
  rw [Bool.or_eq_true] at h
  exact h.imp Nat.eq_of_beq_eq_true Nat.eq_of_beq_eq_true

theorem partnerOf_left (w1 w2 : ℕ) : partnerOf w1 w2 w1 = w2 := by
  unfold partnerOf
  rw [Nat.beq_refl]
  rfl

theorem partnerOf_ne {w1 w2 a : ℕ} (h : a ≠ w1) : partnerOf w1 w2 a = w1 := by
  have hb : Nat.beq a w1 = false := by
    cases hb : Nat.beq a w1 with
    | false => rfl
    | true => exact absurd (Nat.eq_of_beq_eq_true hb) h
  unfold partnerOf
  rw [hb]
  rfl

theorem capLow_zero {q : ℕ} {C : Cert} {Cl : Claim} {J K : Ival} {w : CapW} {a b : ℕ} (hk : w.kind = 0) :
    capLow q C Cl J K w a b = loLeLo J K := by
  unfold capLow
  rw [hk]
  rfl

theorem capLow_one {q : ℕ} {C : Cert} {Cl : Claim} {J K : Ival} {w : CapW} {a b : ℕ} (hk : w.kind = 1) :
    capLow q C Cl J K w a b
      = (Nat.ble 1 w.lq && oneEdge q C w.w1 w.w2 && Nat.ble 1 (Cl.K w.w1 w.w2).hd
          && (inEdge w.w1 w.w2 a && not (Nat.beq (partnerOf w.w1 w.w2 a) b))
          && capIneq J (Cl.K w.w1 w.w2) w.lp w.lq Cl.tp Cl.tq) := by
  unfold capLow
  rw [hk]
  rfl

theorem capLow_two {q : ℕ} {C : Cert} {Cl : Claim} {J K : Ival} {w : CapW} {a b k : ℕ} (hk : w.kind = k + 2) :
    capLow q C Cl J K w a b
      = (Nat.ble 1 w.lq && oneEdge q C w.w1 w.w2 && Nat.ble 1 (Cl.K w.w1 w.w2).hd
          && (inEdge w.w1 w.w2 b && not (Nat.beq (partnerOf w.w1 w.w2 b) a))
          && capIneq J (Cl.K w.w1 w.w2) w.lp w.lq Cl.tp Cl.tq) := by
  unfold capLow
  rw [hk]

theorem supGen_root0 {w : SupW} (h : w.root = 0) :
    supGen w = ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.B, 0, 0, 0, 1⟩, ⟨w.kap, 0, 0, 1, 0⟩, ⟨w.kap, 0, 1, 0, 0⟩]⟩ := by
  unfold supGen
  rw [h]
  rfl

theorem supGen_root1 {w : SupW} (h : w.root = 1) :
    supGen w = ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.kap, 0, 0, 0, 1⟩, ⟨w.B, 0, 0, 1, 0⟩, ⟨w.kap, 0, 1, 0, 0⟩]⟩ := by
  unfold supGen
  rw [h]
  rfl

theorem supGen_root2 {w : SupW} (h : w.root = 2) :
    supGen w = ⟨1, [⟨w.G, 0, 0, 0, 0⟩, ⟨w.kap, 0, 0, 0, 1⟩, ⟨w.kap, 0, 0, 1, 0⟩, ⟨w.B, 0, 1, 0, 0⟩]⟩ := by
  unfold supGen
  rw [h]
  rfl

/-- The value of a polynomial of degree one with nonnegative coefficients. -/
theorem gval_lin (G a b c : ℕ) (u v t : ℝ) :
    gval ⟨1, [⟨G, 0, 0, 0, 0⟩, ⟨a, 0, 0, 0, 1⟩, ⟨b, 0, 0, 1, 0⟩, ⟨c, 0, 1, 0, 0⟩]⟩ u v t
      = (G : ℝ) + a * t + b * v + c * u := by
  simp only [gval, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, pow_zero, pow_one, Nat.cast_zero]
  ring

/-! ## The lists of the check -/

theorem allCuts_iff (f : Cuts → Bool) : ∀ l : List Cuts, allCuts f l = true ↔ ∀ X ∈ l, f X = true
  | [] => ⟨fun _ X hX => by simp at hX, fun _ => rfl⟩
  | X :: l => by
    show (f X && allCuts f l) = true ↔ _
    rw [Bool.and_eq_true, allCuts_iff f l, List.forall_mem_cons]

theorem allGen_iff (f : Gen → Bool) : ∀ l : List Gen, allGen f l = true ↔ ∀ g ∈ l, f g = true
  | [] => ⟨fun _ g hg => by simp at hg, fun _ => rfl⟩
  | g :: l => by
    show (f g && allGen f l) = true ↔ _
    rw [Bool.and_eq_true, allGen_iff f l, List.forall_mem_cons]

theorem anySup_iff (f : SupW → Bool) : ∀ l : List SupW, anySup f l = true ↔ ∃ w ∈ l, f w = true
  | [] => ⟨fun h => absurd (show false = true from h) Bool.false_ne_true, fun ⟨_, hw, _⟩ => by simp at hw⟩
  | w :: l => by
    show (f w || anySup f l) = true ↔ _
    rw [Bool.or_eq_true, anySup_iff f l]
    constructor
    · rintro (h | ⟨v, hv, h⟩)
      · exact ⟨w, List.mem_cons_self, h⟩
      · exact ⟨v, List.mem_cons_of_mem _ hv, h⟩
    · rintro ⟨v, hv, h⟩
      rcases List.mem_cons.mp hv with e | hv
      · left
        rw [← e]
        exact h
      · exact Or.inr ⟨v, hv, h⟩

/-- A cut that `findCuts` returns belongs to an entry of the list with the three classes. -/
theorem findCuts_mem' {a b c : ℕ} {g : Gen} : ∀ {l : List Cuts}, g ∈ findCuts a b c l →
    ∃ X ∈ l, X.a = a ∧ X.b = b ∧ X.c = c ∧ g ∈ X.gens
  | [], h => by
    have h' : g ∈ ([] : List Gen) := h
    simp at h'
  | X :: l, h => by
    rw [findCuts_cons] at h
    cases hk : (Nat.beq X.a a && Nat.beq X.b b && Nat.beq X.c c) with
    | true =>
      rw [hk] at h
      rw [Bool.and_eq_true, Bool.and_eq_true] at hk
      exact ⟨X, List.mem_cons_self, Nat.eq_of_beq_eq_true hk.1.1, Nat.eq_of_beq_eq_true hk.1.2,
        Nat.eq_of_beq_eq_true hk.2, h⟩
    | false =>
      rw [hk] at h
      obtain ⟨Y, hY, hg⟩ := findCuts_mem' (l := l) h
      exact ⟨Y, List.mem_cons_of_mem _ hY, hg⟩

/-! ## Configurations of a claim -/

section Points

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A point of a class of a one-edge type `(w1, w2)` has a partner: another point, of the partner class,
such that the two points form the pair of the type `(w1, w2)`. -/
theorem Labelling.partner {q : ℕ} {C : Cert} {cls : ι → ℕ} (L : Labelling q C cls) {w1 w2 : ℕ}
    (h : oneEdge q C w1 w2 = true) {i : ι} (hi : inEdge w1 w2 (cls i) = true) :
    ∃ i' : ι, i' ≠ i ∧ cls i' = partnerOf w1 w2 (cls i) ∧ w1 ≤ w2
      ∧ ((cls i = w1 ∧ cls i' = w2) ∨ (cls i = w2 ∧ cls i' = w1)) := by
  obtain ⟨hq, h | h⟩ := oneEdge_spec h
  · -- one class of two points
    obtain ⟨e, hn⟩ := h
    have hc : cls i = w1 := by
      rcases inEdge_spec hi with hc | hc
      · exact hc
      · rw [e]
        exact hc
    have hcard : 1 < (univ.filter fun k => cls k = w1).card := by
      have := L.card w1 (by omega)
      omega
    obtain ⟨i', hi', hne⟩ := exists_mem_ne hcard i
    have hc' : cls i' = w1 := (mem_filter.mp hi').2
    refine ⟨i', hne, ?_, by omega, Or.inl ⟨hc, by omega⟩⟩
    rw [hc, partnerOf_left]
    omega
  · -- two classes of one point
    obtain ⟨hlt, hn1, hn2⟩ := h
    rcases inEdge_spec hi with hc | hc
    · have hcard : 0 < (univ.filter fun k => cls k = w2).card := by
        have := L.card w2 hq
        omega
      obtain ⟨i', hi'⟩ := card_pos.mp hcard
      have hc' : cls i' = w2 := (mem_filter.mp hi').2
      refine ⟨i', ?_, ?_, hlt.le, Or.inl ⟨hc, hc'⟩⟩
      · intro e
        rw [e] at hc'
        omega
      · rw [hc, partnerOf_left]
        exact hc'
    · have hcard : 0 < (univ.filter fun k => cls k = w1).card := by
        have := L.card w1 (by omega)
        omega
      obtain ⟨i', hi'⟩ := card_pos.mp hcard
      have hc' : cls i' = w1 := (mem_filter.mp hi').2
      refine ⟨i', ?_, ?_, hlt.le, Or.inr ⟨hc, hc'⟩⟩
      · intro e
        rw [e] at hc'
        omega
      · rw [hc, partnerOf_ne (by omega)]
        exact hc'

/-- Points of the unit sphere of `ℝ⁴` with classes that satisfy a claim: the inner product of every pair
of distinct points lies in the interval `K` of its pair type. -/
structure InClaim (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) (cls : ι → ℕ) (x : ι → EuclideanSpace ℝ (Fin 4)) :
    Prop where
  lab : Labelling q C cls
  unit : ∀ i, ‖x i‖ = 1
  iv : ∀ i j, i ≠ j → cls i ≤ cls j →
    (K (cls i) (cls j)).lo ≤ inner ℝ (x i) (x j) ∧ inner ℝ (x i) (x j) ≤ (K (cls i) (cls j)).hi

variable {P : Params} {C : Cert} {Dm : Dom} {Cl : Claim} {cls : ι → ℕ} {x : ι → EuclideanSpace ℝ (Fin 4)}

theorem claimOk_tq (hcl : claimOk P C Dm Cl = true) : 0 < Cl.tq ∧ Cl.tp < Cl.tq := by
  unfold claimOk at hcl
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hcl
  exact ⟨hcl.1.1.1, hcl.1.1.2⟩

omit [DecidableEq ι] in
/-- The check of the pair type of two distinct points. -/
theorem claimOk_pair (hcl : claimOk P C Dm Cl = true) (L : Labelling P.q C cls) {i j : ι} (hij : i ≠ j)
    (hle : cls i ≤ cls j) :
    0 < (Cl.K (cls i) (cls j)).ld ∧ 0 < (Cl.K (cls i) (cls j)).hd ∧ 0 < (Dm.iv (cls i) (cls j)).ld
      ∧ 0 < (Dm.iv (cls i) (cls j)).hd ∧ hiLe (Cl.K (cls i) (cls j)) Cl.tp Cl.tq = true
      ∧ hiLeHi (Cl.K (cls i) (cls j)) (Dm.iv (cls i) (cls j)) = true
      ∧ capLow P.q C Cl (Dm.iv (cls i) (cls j)) (Cl.K (cls i) (cls j)) (Cl.cap (cls i) (cls j)) (cls i) (cls j)
          = true := by
  unfold claimOk at hcl
  simp only [Bool.and_eq_true] at hcl
  have h : (Nat.blt (cls j) (cls i) || Nat.beq (pcnt C (cls i) (cls j)) 0
      || capOk P.q C Dm Cl (cls i) (cls j)) = true :=
    (all2N_iff _ _).mp hcl.1.2 (cls i) (L.lt i) (cls j) (L.lt j)
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · rw [Nat.blt_eq] at h
    omega
  · exact absurd (Nat.eq_of_beq_eq_true h) (L.pcnt_pos hij).ne'
  · unfold capOk at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

omit [DecidableEq ι] in
/-- All inner products of distinct points of a configuration of a claim are at most the separation bound. -/
theorem claim_le_T (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) {i j : ι} (hij : i ≠ j) :
    inner ℝ (x i) (x j) ≤ (Cl.tp : ℝ) / Cl.tq := by
  have key : ∀ i j : ι, i ≠ j → cls i ≤ cls j → inner ℝ (x i) (x j) ≤ (Cl.tp : ℝ) / Cl.tq := by
    intro i j hij hle
    obtain ⟨_, h2, _, _, h5, _, _⟩ := claimOk_pair hcl hC.lab hij hle
    exact le_trans (hC.iv i j hij hle).2 (hiLe_sound h2 (claimOk_tq hcl).1 h5)
  rcases le_total (cls i) (cls j) with hle | hle
  · exact key i j hij hle
  · rw [real_inner_comm]
    exact key j i (Ne.symm hij) hle

omit [DecidableEq ι] in
/-- The inner product of a point with its partner is at most the upper end of the interval of the one-edge
type. -/
theorem claim_partner (hC : InClaim P.q C Cl.K cls x) {w1 w2 : ℕ} (h : oneEdge P.q C w1 w2 = true) {i : ι}
    (hi : inEdge w1 w2 (cls i) = true) :
    ∃ i' : ι, i' ≠ i ∧ cls i' = partnerOf w1 w2 (cls i) ∧ inner ℝ (x i) (x i') ≤ (Cl.K w1 w2).hi := by
  obtain ⟨i', hne, hc, hle, h | h⟩ := hC.lab.partner h hi
  · refine ⟨i', hne, hc, ?_⟩
    have h3 := (hC.iv i i' (Ne.symm hne) (by omega)).2
    rw [h.1, h.2] at h3
    exact h3
  · refine ⟨i', hne, hc, ?_⟩
    have h3 := (hC.iv i' i hne (by omega)).2
    rw [h.1, h.2, real_inner_comm] at h3
    exact h3

omit [DecidableEq ι] in
/-- The cap bound at two points: if the point `i` has a partner in the one-edge type `(w1, w2)` whose class
differs from the class of `j`, and the check `capIneq` succeeds for an interval `J`, then the inner product
of the two points is at least the lower end of `J`. -/
theorem claim_cap (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) {J : Ival} {w : CapW}
    {i j : ι} (hJ : 0 < J.ld) (hlq : 0 < w.lq) (hone : oneEdge P.q C w.w1 w.w2 = true)
    (hhd : 0 < (Cl.K w.w1 w.w2).hd) (hin : inEdge w.w1 w.w2 (cls i) = true)
    (hpn : partnerOf w.w1 w.w2 (cls i) ≠ cls j)
    (hcap : capIneq J (Cl.K w.w1 w.w2) w.lp w.lq Cl.tp Cl.tq = true) : J.lo ≤ inner ℝ (x i) (x j) := by
  obtain ⟨i', _, hc, hpart⟩ := claim_partner hC hone hin
  have hji : i' ≠ j := fun e => hpn (by rw [← e]; exact hc.symm)
  have hT := claim_le_T hcl hC hji
  obtain ⟨m, hm0, hm1, hm2⟩ := capIneq_sound hJ hlq (claimOk_tq hcl).1 hhd hcap
  have hpp : inner ℝ (x i) (x i') ≤ -(-(Cl.K w.w1 w.w2).hi) := by
    rw [neg_neg]
    exact hpart
  have h := cap_witness (x i) (x i') (x j) (hC.unit i) (hC.unit i') (hC.unit j) hpp hT (by positivity) hm0 hm1
  rw [hm2]
  exact h

omit [DecidableEq ι] in
/-- **(D1).** The inner product of two distinct points lies in the interval of the domain. -/
theorem claim_iv (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) {i j : ι} (hij : i ≠ j)
    (hle : cls i ≤ cls j) :
    (Dm.iv (cls i) (cls j)).lo ≤ inner ℝ (x i) (x j) ∧ inner ℝ (x i) (x j) ≤ (Dm.iv (cls i) (cls j)).hi := by
  obtain ⟨hKl, hKh, hJl, hJh, _, h6, h7⟩ := claimOk_pair hcl hC.lab hij hle
  obtain ⟨hlo, hhi⟩ := hC.iv i j hij hle
  refine ⟨?_, le_trans hhi (hiLeHi_sound hKh hJh h6)⟩
  have hkind : (Cl.cap (cls i) (cls j)).kind = 0 ∨ (Cl.cap (cls i) (cls j)).kind = 1
      ∨ 2 ≤ (Cl.cap (cls i) (cls j)).kind := by omega
  rcases hkind with hk | hk | hk
  · rw [capLow_zero hk] at h7
    exact le_trans (loLeLo_sound hJl hKl h7) hlo
  · rw [capLow_one hk] at h7
    simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at h7
    obtain ⟨⟨⟨⟨hlq, hone⟩, hhd⟩, hin, hpn⟩, hcap⟩ := h7
    exact claim_cap hcl hC hJl hlq hone hhd hin (Nat.ne_of_beq_eq_false hpn) hcap
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hk
    rw [capLow_two hk] at h7
    simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at h7
    obtain ⟨⟨⟨⟨hlq, hone⟩, hhd⟩, hin, hpn⟩, hcap⟩ := h7
    have h := claim_cap hcl hC hJl hlq hone hhd hin (Nat.ne_of_beq_eq_false hpn) hcap
    rw [real_inner_comm] at h
    exact h

omit [DecidableEq ι] in
/-- The support inequality at a root `r` whose partner in the one-edge type of the witness has a class
different from those of the two other points, in the integers of the witness. -/
theorem claim_support (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) {w : SupW} {r s1 s2 : ι}
    (hone : oneEdge P.q C w.w1 w.w2 = true) (hin : inEdge w.w1 w.w2 (cls r) = true)
    (h1 : partnerOf w.w1 w.w2 (cls r) ≠ cls s1) (h2 : partnerOf w.w1 w.w2 (cls r) ≠ cls s2)
    (hk : 0 < w.kap) (hB : 0 < w.B) (haq : 0 < w.aq) (hhd : 0 < (Cl.K w.w1 w.w2).hd)
    (hs : supIneq (Cl.K w.w1 w.w2) w Cl.tp Cl.tq = true) :
    0 ≤ (w.G : ℝ) + w.B * inner ℝ (x s1) (x s2) + w.kap * (inner ℝ (x r) (x s1) + inner ℝ (x r) (x s2)) := by
  obtain ⟨r', _, hc, hpart⟩ := claim_partner hC hone hin
  have hr1 : r' ≠ s1 := fun e => h1 (by rw [← e]; exact hc.symm)
  have hr2 : r' ≠ s2 := fun e => h2 (by rw [← e]; exact hc.symm)
  have hT1 := claim_le_T hcl hC hr1
  have hT2 := claim_le_T hcl hC hr2
  have hpp : inner ℝ (x r) (x r') ≤ -(-(Cl.K w.w1 w.w2).hi) := by
    rw [neg_neg]
    exact hpart
  have hkR : (0 : ℝ) < w.kap := Nat.cast_pos.mpr hk
  have hBR : (0 : ℝ) < w.B := Nat.cast_pos.mpr hB
  have hsup := support_witness (x r) (x r') (x s1) (x s2) (hC.unit r) (hC.unit r') (hC.unit s1) (hC.unit s2)
    (a := (w.ap : ℝ) / w.aq) (b := (w.B : ℝ) / w.kap) hpp hT1 hT2 (by positivity) (by positivity)
  have hG := supIneq_sound hk hB haq (claimOk_tq hcl).1 hhd hs
  have h3 : 0 ≤ inner ℝ (x r) (x s1) + inner ℝ (x r) (x s2) + (w.B : ℝ) / w.kap * inner ℝ (x s1) (x s2)
      + (w.G : ℝ) / w.kap := by linarith
  have e1 : (w.kap : ℝ) * ((w.B : ℝ) / w.kap) = w.B := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hkR.ne'
  have e2 : (w.kap : ℝ) * ((w.G : ℝ) / w.kap) = w.G := by
    rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hkR.ne'
  have h4 := mul_nonneg hkR.le h3
  have e : (w.kap : ℝ) * (inner ℝ (x r) (x s1) + inner ℝ (x r) (x s2)
        + (w.B : ℝ) / w.kap * inner ℝ (x s1) (x s2) + (w.G : ℝ) / w.kap)
      = (w.kap : ℝ) * (inner ℝ (x r) (x s1) + inner ℝ (x r) (x s2))
        + (w.kap : ℝ) * ((w.B : ℝ) / w.kap) * inner ℝ (x s1) (x s2) + (w.kap : ℝ) * ((w.G : ℝ) / w.kap) := by ring
  rw [e, e1, e2] at h4
  linarith

omit [DecidableEq ι] in
/-- **(D2).** Every cut of the domain is nonnegative at the three inner products of a triple with
nondecreasing classes. -/
theorem claim_cuts (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) {i j k : ι} {g : Gen}
    (hg : g ∈ findCuts (cls i) (cls j) (cls k) Dm.cuts) :
    0 ≤ gval g (inner ℝ (x i) (x j)) (inner ℝ (x i) (x k)) (inner ℝ (x j) (x k)) := by
  obtain ⟨X, hX, ea, eb, ec, hgX⟩ := findCuts_mem' hg
  have hall := hcl
  unfold claimOk at hall
  simp only [Bool.and_eq_true] at hall
  obtain ⟨w, _, hw⟩ := (anySup_iff _ _).mp ((allGen_iff _ _).mp ((allCuts_iff _ _).mp hall.2 X hX) g hgX)
  rw [ea, eb, ec] at hw
  unfold supOk at hw
  simp only [Bool.and_eq_true, Nat.ble_eq, Bool.not_eq_true'] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hgen, hroot⟩, hk⟩, hB⟩, haq⟩, hone⟩, hin⟩, hp1⟩, hp2⟩, hhd⟩, hs⟩ := hw
  have eg := genBeq_eq hgen
  have hr : w.root = 0 ∨ w.root = 1 ∨ w.root = 2 := by omega
  rcases hr with hr | hr | hr
  · -- the root is the first point
    rw [hr] at hin hp1 hp2
    have h := claim_support hcl hC (r := i) (s1 := j) (s2 := k) hone hin (Nat.ne_of_beq_eq_false hp1)
      (Nat.ne_of_beq_eq_false hp2) hk hB haq hhd hs
    rw [eg, supGen_root0 hr, gval_lin]
    linarith
  · -- the root is the second point
    rw [hr] at hin hp1 hp2
    have h := claim_support hcl hC (r := j) (s1 := i) (s2 := k) hone hin (Nat.ne_of_beq_eq_false hp1)
      (Nat.ne_of_beq_eq_false hp2) hk hB haq hhd hs
    rw [real_inner_comm (x i) (x j)] at h
    rw [eg, supGen_root1 hr, gval_lin]
    linarith
  · -- the root is the third point
    rw [hr] at hin hp1 hp2
    have h := claim_support hcl hC (r := k) (s1 := i) (s2 := j) hone hin (Nat.ne_of_beq_eq_false hp1)
      (Nat.ne_of_beq_eq_false hp2) hk hB haq hhd hs
    rw [real_inner_comm (x i) (x k), real_inner_comm (x j) (x k)] at h
    rw [eg, supGen_root2 hr, gval_lin]
    linarith

omit [DecidableEq ι] in
/-- **The declared domain contains the claim.** -/
theorem inSource_of_claim (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) :
    InSource P.q C Dm cls x where
  lab := hC.lab
  unit := hC.unit
  inj := by
    intro i j e
    by_contra hij
    have h1 := claim_le_T hcl hC hij
    have h2 : (Cl.tp : ℝ) / Cl.tq < 1 := by
      have hlt : (Cl.tp : ℝ) < Cl.tq := by exact_mod_cast (claimOk_tq hcl).2
      exact (div_lt_one (Nat.cast_pos.mpr (claimOk_tq hcl).1)).mpr hlt
    rw [e, real_inner_self_eq_norm_sq, hC.unit j] at h1
    linarith
  iv := fun _ _ hij hle => claim_iv hcl hC hij hle
  cuts := fun _ _ _ _ _ _ _ hg => claim_cuts hcl hC hg

end Points

/-- **The theorem of a certificate for a claim.** If the domain of a typed certificate contains a claim,
then the energy of every configuration of the claim exceeds `tp / tq`. -/
theorem energy_gt_claim {P : Params} {C : Cert} {xs : List TyX} {Dm : Dom} {Cl : Claim} {sP M tp tq n : ℕ}
    {cls : Fin n → ℕ} {x : Fin n → EuclideanSpace ℝ (Fin 4)} (H : CertHolds P C xs)
    (hdom : domOk P C Dm xs = true) (hmin : Minorant P C Dm sP) (hb : boundOk P C xs sP M tp tq = true)
    (hcl : claimOk P C Dm Cl = true) (hC : InClaim P.q C Cl.K cls x) :
    (tp : ℝ) / tq < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 :=
  energy_gt_fin H hdom hmin hb (inSource_of_claim hcl hC)

end CAP.Wsos
