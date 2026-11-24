module

public import S3N9.Cells54
public import S3N9.Fit

/-!
# The theorem for nine points: the cell L3-k2 before its core

The cell L3-k2 of the source consists of the configurations with exactly two near pairs, both with an inner
product of at most `-99 / 100`. For a chain `y` (`S3N9.IsChain`) these are the pairs of the positions `(0, 1)` and
`(2, 3)`: the pairs `A` and `B`. This file follows Section 6 of the source up to the core (row A6 of
`S3N9/README.md`).

* `ring_split` (`lma:ringsplit`): the chain lies in one of the pair claims *main*, *aux1* (`claimsRing`), or in the
  claim *aux2* (`Aux2`): the pairs `C`, `D` of the positions `(4, 5)`, `(6, 7)` have inner products of at most
  `-3 / 4`.
* `Aux2.comp`: the claim *aux2* is invariant under a relabelling that respects the pairs (`Respects`).
* `exists_bent` (`lma:morebent`): a labelling in *aux2* with `t_B ≤ t_A`.
* `SC`, `InSC`, `claimsSel` (`def:selclaim`): the four selected-edge claims. `inClaim_of_SC`: a labelled
  configuration in a selected-edge claim satisfies the hypothesis of a typed certificate with the classes
  `{a}, {a'}, {b}, {b'}, C, D, {x}` whose claim contains it (`scFits`, decided by the kernel).
* `sel_of_tilt` (`lma:seledge`): if an inner product between `A` and `B` is large in absolute value, a relabelling
  inside `A` and `B` lies in a selected-edge claim.
* `sel_or_core` (`lma:split2`): a labelling in *aux2* with `t_B ≤ t_A` has a relabelling in a selected-edge claim,
  or it lies in the core (`Core`): all inner products between `A` and `B` are at most `3 / 10` in absolute value.
* `l3k2_outer`: the three statements together, for a chain.
-/

@[expose] public section

namespace S3N9

open CAP.Wsos

/-! ## The claims of the ring split -/

namespace Cell

/-- The inner cap `c_in = -997 / 1000`. -/
def cin : ℤ := -1994

/-- The claim *main* (`lma:ringsplit` (i)): the pairs `A`, `B`, and five points with inner products of at least
`-3 / 4`. -/
def ringMain : PC := ⟨[(m1, a1), (m1, a1)], -1500⟩

/-- The claim *aux1* (`lma:ringsplit` (ii)): the pairs `A`, `B`, a pair `C` with an inner product of at most
`-3 / 4`, and three points with inner products of at least `-3 / 4`. -/
def ringAux : PC := ⟨[(m1, a1), (m1, a1), (th, -1500)], -1500⟩

end Cell

/-- The pair claims of the cell L3-k2. -/
def claimsRing : List PC := [Cell.ringMain, Cell.ringAux]

theorem cin_eq : ((Cell.cin : ℤ) : ℝ) / 2000 = -997 / 1000 := by norm_num [Cell.cin]

/-! ## The claim aux2 -/

/-- The pair of a position: the positions `2 c` and `2 c + 1` form the pair `c`. The pairs `0, 1, 2, 3` are `A`,
`B`, `C`, `D`; the position `8` is alone. -/
def pr (m : Fin 9) : ℕ := m.val / 2

/-- **The claim aux2** (`lma:ringsplit` (iii)) for a labelled configuration: unit vectors, separated; the pairs `A`
and `B` have inner products of at most `-99 / 100`, the pairs `C` and `D` of at most `-3 / 4`, and every pair of
points other than `A` and `B` has an inner product above `-9 / 10`. -/
structure Aux2 (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  unit : ∀ m, ‖y m‖ = 1
  sep : Separated y
  near : ∀ m n : Fin 9, m ≠ n → pr m = pr n → pr m < 2 → inner ℝ (y m) (y n) ≤ -(99 : ℝ) / 100
  mid : ∀ m n : Fin 9, m ≠ n → pr m = pr n → 2 ≤ pr m → inner ℝ (y m) (y n) ≤ -(3 : ℝ) / 4
  far : ∀ m n : Fin 9, m ≠ n → pr m ≠ pr n ∨ 2 ≤ pr m → -(9 : ℝ) / 10 < inner ℝ (y m) (y n)

/-- A permutation of the positions that maps pairs to pairs, and the pairs `A`, `B` to `A`, `B`. -/
def Respects (σ : Equiv.Perm (Fin 9)) : Prop :=
  (∀ m n : Fin 9, pr (σ m) = pr (σ n) ↔ pr m = pr n) ∧ ∀ m : Fin 9, pr (σ m) < 2 ↔ pr m < 2

instance (σ : Equiv.Perm (Fin 9)) : Decidable (Respects σ) := by
  unfold Respects
  infer_instance

/-- **The claim aux2 is invariant under a relabelling that respects the pairs.** -/
theorem Aux2.comp {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) {σ : Equiv.Perm (Fin 9)}
    (hσ : Respects σ) : Aux2 (y ∘ σ) where
  unit := fun m => h.unit (σ m)
  sep := fun i j hij => h.sep (σ i) (σ j) (σ.injective.ne hij)
  near := fun m n hmn hp hl =>
    h.near (σ m) (σ n) (σ.injective.ne hmn) ((hσ.1 m n).2 hp) ((hσ.2 m).2 hl)
  mid := fun m n hmn hp hl =>
    h.mid (σ m) (σ n) (σ.injective.ne hmn) ((hσ.1 m n).2 hp) (by
      have := hσ.2 m
      omega)
  far := fun m n hmn hp => h.far (σ m) (σ n) (σ.injective.ne hmn) (by
    rcases hp with hp | hp
    · exact Or.inl fun e => hp ((hσ.1 m n).1 e)
    · right
      have := hσ.2 m
      omega)

/-- The inner product of the two points of a pair. -/
theorem inner_eq_mval {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} {m n : Fin 9} (hmn : m ≠ n) (hp : pr m = pr n) :
    inner ℝ (y m) (y n) = mval y (pr m) := by
  unfold pr at hp ⊢
  have hm := m.isLt
  have hn := n.isLt
  have hne : m.val ≠ n.val := fun h => hmn (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact mval_eq (by omega) (by omega)
  · rw [real_inner_comm]
    exact mval_eq (c := m.val / 2) (a := n) (b := m) (by omega) (by omega)

theorem inner_pair {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} {m n : Fin 9} {c : ℕ} (hmn : m ≠ n) (hm : pr m = c)
    (hn : pr n = c) : inner ℝ (y m) (y n) = mval y c := by
  rw [inner_eq_mval hmn (hm.trans hn.symm), hm]

/-- The inner product of a pair after a relabelling that maps the pair `c` to the pair `c'`. -/
theorem mval_comp {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (σ : Equiv.Perm (Fin 9)) {c c' : ℕ} (hc : c < 4)
    (h : ∀ m : Fin 9, pr m = c → pr (σ m) = c') : mval (y ∘ σ) c = mval y c' := by
  obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * c := ⟨⟨2 * c, by omega⟩, rfl⟩
  obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * c + 1 := ⟨⟨2 * c + 1, by omega⟩, rfl⟩
  rw [← mval_eq (y := y ∘ σ) ha hb]
  have hab : a ≠ b := fun e => by
    have := congrArg Fin.val e
    omega
  exact inner_pair (σ.injective.ne hab) (h a (by unfold pr; omega)) (h b (by unfold pr; omega))

/-- **A chain with two near pairs whose third and fourth pairs have inner products of at most `-3 / 4` lies in
aux2.** -/
theorem aux2_of_chain {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) (h0 : mval y 0 ≤ -(99 : ℝ) / 100) (h1 : mval y 1 ≤ -(99 : ℝ) / 100)
    (hf2 : -(9 : ℝ) / 10 < mval y 2) (h2 : mval y 2 ≤ -(3 : ℝ) / 4) (h3 : mval y 3 ≤ -(3 : ℝ) / 4) : Aux2 y where
  unit := hu
  sep := hs
  near := fun m n hmn hp hl => by
    rw [inner_eq_mval hmn hp]
    obtain ⟨c, hc'⟩ : ∃ c, pr m = c := ⟨_, rfl⟩
    rw [hc'] at hl ⊢
    interval_cases c
    · exact h0
    · exact h1
  mid := fun m n hmn hp hl => by
    rw [inner_eq_mval hmn hp]
    have h4 : pr m < 4 := by
      unfold pr at hp ⊢
      have hne : m.val ≠ n.val := fun e => hmn (Fin.ext e)
      have hm := m.isLt
      have hn := n.isLt
      omega
    obtain ⟨c, hc'⟩ : ∃ c, pr m = c := ⟨_, rfl⟩
    rw [hc'] at hl h4 ⊢
    interval_cases c
    · exact h2
    · exact h3
  far := fun m n hmn hp => by
    refine chain_far hu hs hc (k := 2) (by norm_num) ?_ ?_ hmn ?_
    · intro c hc' a b ha hb
      rw [mval_eq ha hb]
      interval_cases c <;> linarith
    · intro _ a b ha hb
      rw [mval_eq ha hb]
      exact hf2
    · unfold pr at hp
      rcases hp with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by omega)

/-- **The ring split** (`lma:ringsplit`). A chain with exactly two near pairs, both with an inner product of at
most `-99 / 100`, lies in the claim *main*, in the claim *aux1*, or in the claim *aux2*. -/
theorem ring_split {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) (h0 : mval y 0 ≤ -(99 : ℝ) / 100) (h1 : mval y 1 ≤ -(99 : ℝ) / 100)
    (hf2 : -(9 : ℝ) / 10 < mval y 2) : (∃ c ∈ claimsRing, InPC c y) ∨ Aux2 y := by
  have hnear : ∀ i < 2, mval y i ≤ -(9 : ℝ) / 10 := fun i hi => by
    interval_cases i <;> linarith
  have hfar : 2 < 4 → -(9 : ℝ) / 10 < mval y 2 := fun _ => hf2
  have i0 := ivl (m := mval y 0) (a := Cell.m1) (b := Cell.a1)
    (by rw [m1_eq]; exact neg_one_le_mval hu (by norm_num)) (by rw [a1_eq]; exact h0)
  have i1 := ivl (m := mval y 1) (a := Cell.m1) (b := Cell.a1)
    (by rw [m1_eq]; exact neg_one_le_mval hu (by norm_num)) (by rw [a1_eq]; exact h1)
  have e34 : ((-1500 : ℤ) : ℝ) / 2000 = -3 / 4 := by norm_num
  by_cases ha : -(3 : ℝ) / 4 ≤ mval y 2
  · exact Or.inl ⟨Cell.ringMain, by decide,
      inPC2 hu hs hc hnear hfar le_rfl i0 i1 (by rw [e34]; linarith)⟩
  · rw [not_le] at ha
    by_cases hb : -(3 : ℝ) / 4 ≤ mval y 3
    · exact Or.inl ⟨Cell.ringAux, by decide,
        inPC3 hu hs hc hnear hfar (by norm_num) i0 i1
          (ivl (a := Cell.th) (b := -1500) (by rw [th_eq]; linarith) (by rw [e34]; linarith))
          (by rw [e34]; linarith)⟩
    · rw [not_le] at hb
      exact Or.inr (aux2_of_chain hu hs hc h0 h1 hf2 (le_of_lt ha) (le_of_lt hb))

/-- **A labelling in aux2 with `t_B ≤ t_A`** (`lma:morebent`). -/
theorem exists_bent {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) :
    ∃ σ : Equiv.Perm (Fin 9), Aux2 (y ∘ σ) ∧ mval (y ∘ σ) 1 ≤ mval (y ∘ σ) 0 := by
  by_cases hb : mval y 1 ≤ mval y 0
  · refine ⟨1, ?_⟩
    rw [Equiv.Perm.coe_one, Function.comp_id]
    exact ⟨h, hb⟩
  · rw [not_le] at hb
    refine ⟨Equiv.swap 0 2 * Equiv.swap 1 3, h.comp (by decide +kernel), ?_⟩
    rw [mval_comp (c := 1) (c' := 0) _ (by norm_num) (by decide +kernel),
      mval_comp (c := 0) (c' := 1) _ (by norm_num) (by decide +kernel)]
    exact le_of_lt hb

/-! ## The selected-edge claims -/

/-- A selected-edge claim (`def:selclaim`): the intervals of the pairs `A`, `B` and of the selected edge, in
units of `1 / 2000`. -/
structure SC where
  jA : ℤ × ℤ
  jB : ℤ × ℤ
  e : ℤ × ℤ
deriving DecidableEq, Repr

/-- A labelled configuration in a selected-edge claim: it lies in aux2; the positions `0, 1` are `a, a'`, the
positions `2, 3` are `b, b'`, and the selected edge is the pair of the positions `0, 2`. -/
structure InSC (c : SC) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  aux : Aux2 y
  tA : (c.jA.1 : ℝ) / 2000 ≤ inner ℝ (y 0) (y 1) ∧ inner ℝ (y 0) (y 1) ≤ (c.jA.2 : ℝ) / 2000
  tB : (c.jB.1 : ℝ) / 2000 ≤ inner ℝ (y 2) (y 3) ∧ inner ℝ (y 2) (y 3) ≤ (c.jB.2 : ℝ) / 2000
  edge : (c.e.1 : ℝ) / 2000 ≤ inner ℝ (y 0) (y 2) ∧ inner ℝ (y 0) (y 2) ≤ (c.e.2 : ℝ) / 2000

namespace Cell

/-- The leaf `Q2+in`: both pairs are inner, and the selected edge is at least `1 / 10`. -/
def q2p : SC := ⟨(m1, cin), (m1, cin), (200, 1089)⟩
/-- The leaf `Q2-in`. -/
def q2m : SC := ⟨(m1, cin), (m1, cin), (th, -200)⟩
/-- The leaf `Q1At30+`: the pair `A` is in the shell, and the selected edge is at least `3 / 10`. -/
def q1p : SC := ⟨(cin, a1), (m1, a1), (600, 1089)⟩
/-- The leaf `Q1At30-`. -/
def q1m : SC := ⟨(cin, a1), (m1, a1), (th, -600)⟩

end Cell

/-- The four selected-edge claims of the cell L3-k2. -/
def claimsSel : List SC := [Cell.q2p, Cell.q2m, Cell.q1p, Cell.q1m]

/-- The classes of a selected-edge claim: `{a}, {a'}, {b}, {b'}, C, D, {x}`. -/
def clsS (m : Fin 9) : ℕ := if m.val < 4 then m.val else if m.val < 8 then m.val / 2 + 2 else 6

theorem clsS_lt : ∀ m : Fin 9, clsS m < 7 := by decide

theorem clsS_low : ∀ m : Fin 9, clsS m < 4 → m.val = clsS m := by decide

theorem clsS_same : ∀ i j : Fin 9, i ≠ j → clsS i = clsS j →
    pr i = pr j ∧ 2 ≤ pr i ∧ (clsS i = 4 ∨ clsS i = 5) := by decide +kernel

theorem clsS_far : ∀ i j : Fin 9, clsS i < clsS j → ¬ (clsS i = 0 ∧ clsS j = 1) → ¬ (clsS i = 2 ∧ clsS j = 3) →
    pr i ≠ pr j ∨ 2 ≤ pr i := by decide +kernel

theorem card_clsS : ∀ x < 7, (Finset.univ.filter fun k : Fin 9 => clsS k = x).card
    = if x = 4 ∨ x = 5 then 2 else 1 := by decide +kernel

/-- The claim `K` of a certificate with the classes `C.n` has the classes of a selected-edge claim and contains
the intervals of the claim `c`. -/
def scFits (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) (c : SC) : Prop :=
  q = 7 ∧ (∀ x < 7, C.n x = if x = 4 ∨ x = 5 then 2 else 1)
    ∧ ivalFits (K 0 1) c.jA.1 c.jA.2 ∧ ivalFits (K 2 3) c.jB.1 c.jB.2 ∧ ivalFits (K 0 2) c.e.1 c.e.2
    ∧ ivalFits (K 4 4) (-1800) (-1500) ∧ ivalFits (K 5 5) (-1800) (-1500)
    ∧ ∀ c2 < 7, ∀ c1 < c2, (c1 = 0 ∧ c2 = 1) ∨ (c1 = 2 ∧ c2 = 3) ∨ (c1 = 0 ∧ c2 = 2)
      ∨ ivalFits (K c1 c2) (-1800) 1089

instance (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) (c : SC) : Decidable (scFits q C K c) := by
  unfold scFits
  infer_instance

/-- **A selected-edge claim of the paper in a claim of a certificate.** -/
theorem inClaim_of_SC {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {c : SC} {y : Fin 9 → EuclideanSpace ℝ (Fin 4)}
    (hf : scFits q C K c) (h : InSC c y) : InClaim q C K clsS y := by
  obtain ⟨hq, hn, fA, fB, fE, f4, f5, fo⟩ := hf
  have rA := ivalFits_real fA
  have rB := ivalFits_real fB
  have rE := ivalFits_real fE
  have r4 := ivalFits_real f4
  have r5 := ivalFits_real f5
  push_cast at r4 r5
  refine ⟨⟨fun m => ?_, fun x hx => ?_⟩, h.aux.unit, fun i j hij hle => ?_⟩
  · rw [hq]
    exact clsS_lt m
  · rw [hq] at hx
    rw [card_clsS x hx, hn x hx]
  · rcases Nat.lt_or_ge (clsS i) (clsS j) with hlt | hge
    · by_cases c01 : clsS i = 0 ∧ clsS j = 1
      · have hi : i = 0 := Fin.ext ((clsS_low i (by omega)).trans c01.1)
        have hj : j = 1 := Fin.ext ((clsS_low j (by omega)).trans c01.2)
        rw [c01.1, c01.2, hi, hj]
        exact ⟨le_trans rA.1 h.tA.1, le_trans h.tA.2 rA.2⟩
      by_cases c23 : clsS i = 2 ∧ clsS j = 3
      · have hi : i = 2 := Fin.ext ((clsS_low i (by omega)).trans c23.1)
        have hj : j = 3 := Fin.ext ((clsS_low j (by omega)).trans c23.2)
        rw [c23.1, c23.2, hi, hj]
        exact ⟨le_trans rB.1 h.tB.1, le_trans h.tB.2 rB.2⟩
      by_cases c02 : clsS i = 0 ∧ clsS j = 2
      · have hi : i = 0 := Fin.ext ((clsS_low i (by omega)).trans c02.1)
        have hj : j = 2 := Fin.ext ((clsS_low j (by omega)).trans c02.2)
        rw [c02.1, c02.2, hi, hj]
        exact ⟨le_trans rE.1 h.edge.1, le_trans h.edge.2 rE.2⟩
      have r := ivalFits_real
        (((((fo (clsS j) (clsS_lt j) (clsS i) hlt).resolve_left c01).resolve_left c23).resolve_left c02))
      push_cast at r
      have lo := h.aux.far i j hij (clsS_far i j hlt c01 c23)
      have hi := h.aux.sep i j hij
      exact ⟨by linarith [r.1], by linarith [r.2]⟩
    · have heq : clsS i = clsS j := le_antisymm hle hge
      obtain ⟨hp, h2, h45⟩ := clsS_same i j hij heq
      have lo := h.aux.far i j hij (Or.inr h2)
      have hi := h.aux.mid i j hij hp h2
      rw [← heq]
      rcases h45 with e | e
      · rw [e]
        exact ⟨by linarith [r4.1], by linarith [r4.2]⟩
      · rw [e]
        exact ⟨by linarith [r5.1], by linarith [r5.2]⟩

/-- The energy exceeds `35 / 2` on every selected-edge claim of the list `l`. -/
def ExclSel (l : List SC) : Prop :=
  ∀ c ∈ l, ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InSC c y → (35 : ℝ) / 2 < energyE y

theorem exclSel_nil : ExclSel [] := fun _ hc => absurd hc List.not_mem_nil

theorem exclSel_cons {a : SC} {l : List SC}
    (ha : ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InSC a y → (35 : ℝ) / 2 < energyE y) (hl : ExclSel l) :
    ExclSel (a :: l) := by
  intro c hc y hy
  rcases List.mem_cons.1 hc with rfl | h
  · exact ha y hy
  · exact hl c h y hy

/-- **The theorem of a claim of a certificate excludes a selected-edge claim of the paper.** -/
theorem exclSel_of_cert {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {c : SC} (hf : scFits q C K c)
    (hE : ∀ {cls : Fin 9 → ℕ} {x : Fin 9 → EuclideanSpace ℝ (Fin 4)}, InClaim q C K cls x →
      (35 : ℝ) / 2 < ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2) :
    ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InSC c y → (35 : ℝ) / 2 < energyE y :=
  fun _ h => hE (inClaim_of_SC hf h)

/-! ## The split of aux2 by the inner products between the pairs `A` and `B` -/

/-- A labelling in aux2 whose selected edge is at least `d / 2000` in absolute value lies in the selected-edge
claim of its sign. -/
theorem inSC_of_edge {z : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 z) {jA jB : ℤ × ℤ} {d : ℤ}
    (hA : (jA.1 : ℝ) / 2000 ≤ inner ℝ (z 0) (z 1) ∧ inner ℝ (z 0) (z 1) ≤ (jA.2 : ℝ) / 2000)
    (hB : (jB.1 : ℝ) / 2000 ≤ inner ℝ (z 2) (z 3) ∧ inner ℝ (z 2) (z 3) ≤ (jB.2 : ℝ) / 2000)
    (hd : (d : ℝ) / 2000 ≤ |inner ℝ (z 0) (z 2)|) :
    InSC ⟨jA, jB, (d, 1089)⟩ z ∨ InSC ⟨jA, jB, (Cell.th, -d)⟩ z := by
  have hsep := h.sep 0 2 (by decide)
  have hfar := h.far 0 2 (by decide) (Or.inl (by decide))
  rcases le_abs.1 hd with h1 | h1
  · refine Or.inl ⟨h, hA, hB, h1, ?_⟩
    show inner ℝ (z 0) (z 2) ≤ ((1089 : ℤ) : ℝ) / 2000
    push_cast
    linarith
  · refine Or.inr ⟨h, hA, hB, ?_, ?_⟩
    · show ((Cell.th : ℤ) : ℝ) / 2000 ≤ inner ℝ (z 0) (z 2)
      rw [th_eq]
      linarith
    · show inner ℝ (z 0) (z 2) ≤ ((-d : ℤ) : ℝ) / 2000
      push_cast
      linarith

/-- A relabelling inside the pairs `A` and `B` that moves the positions `i` and `j` to the positions `0` and
`2`. -/
theorem selPerm_spec : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 →
    Respects (Equiv.swap 0 i * Equiv.swap 2 j) ∧ (Equiv.swap 0 i * Equiv.swap 2 j) 0 = i
      ∧ (Equiv.swap 0 i * Equiv.swap 2 j) 2 = j
      ∧ pr ((Equiv.swap 0 i * Equiv.swap 2 j) 1) = 0
      ∧ (Equiv.swap 0 i * Equiv.swap 2 j) 1 ≠ (Equiv.swap 0 i * Equiv.swap 2 j) 0
      ∧ pr ((Equiv.swap 0 i * Equiv.swap 2 j) 3) = 1
      ∧ (Equiv.swap 0 i * Equiv.swap 2 j) 3 ≠ (Equiv.swap 0 i * Equiv.swap 2 j) 2 := by
  decide +kernel

/-- **The selected edge** (`lma:seledge`). If the inner product of a point of `A` and a point of `B` is at least
`d / 2000` in absolute value, a relabelling inside `A` and `B` lies in one of the two selected-edge claims with
this bound. -/
theorem sel_of_tilt {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) {jA jB : ℤ × ℤ} {d : ℤ}
    (hA : (jA.1 : ℝ) / 2000 ≤ mval y 0 ∧ mval y 0 ≤ (jA.2 : ℝ) / 2000)
    (hB : (jB.1 : ℝ) / 2000 ≤ mval y 1 ∧ mval y 1 ≤ (jB.2 : ℝ) / 2000)
    {i j : Fin 9} (hi : i.val < 2) (hj2 : 2 ≤ j.val) (hj4 : j.val < 4)
    (hd : (d : ℝ) / 2000 ≤ |inner ℝ (y i) (y j)|) :
    ∃ σ : Equiv.Perm (Fin 9), InSC ⟨jA, jB, (d, 1089)⟩ (y ∘ σ) ∨ InSC ⟨jA, jB, (Cell.th, -d)⟩ (y ∘ σ) := by
  obtain ⟨hσ, e0, e2, p1, n1, p3, n3⟩ := selPerm_spec i j hi hj2 hj4
  refine ⟨Equiv.swap 0 i * Equiv.swap 2 j, inSC_of_edge (h.comp hσ) ?_ ?_ ?_⟩
  · simp only [Function.comp_apply]
    rw [inner_pair (c := 0) n1.symm (by rw [e0]; unfold pr; omega) p1]
    exact hA
  · simp only [Function.comp_apply]
    rw [inner_pair (c := 1) n3.symm (by rw [e2]; unfold pr; omega) p3]
    exact hB
  · simp only [Function.comp_apply]
    rw [e0, e2]
    exact hd

/-- **The core of the cell L3-k2** for a labelled configuration: it lies in aux2, `t_B ≤ t_A`, and the inner
products between the pairs `A` and `B` are at most `3 / 10` in absolute value. -/
structure Core (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  aux : Aux2 y
  bent : mval y 1 ≤ mval y 0
  tilt : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → |inner ℝ (y i) (y j)| ≤ 3 / 10

theorem mval_zero_near {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) : mval y 0 ≤ -(99 : ℝ) / 100 := by
  rw [← inner_pair (y := y) (m := 0) (n := 1) (c := 0) (by decide) (by decide) (by decide)]
  exact h.near 0 1 (by decide) (by decide) (by decide)

theorem mval_one_near {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) : mval y 1 ≤ -(99 : ℝ) / 100 := by
  rw [← inner_pair (y := y) (m := 2) (n := 3) (c := 1) (by decide) (by decide) (by decide)]
  exact h.near 2 3 (by decide) (by decide) (by decide)

/-- **The split of aux2** (`lma:split2`, `lma:seledge`). A labelling in aux2 with `t_B ≤ t_A` has a relabelling in
one of the four selected-edge claims, or it lies in the core. -/
theorem sel_or_core {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (h : Aux2 y) (hb : mval y 1 ≤ mval y 0) :
    (∃ σ : Equiv.Perm (Fin 9), ∃ c ∈ claimsSel, InSC c (y ∘ σ)) ∨ Core y := by
  by_cases ht : ∀ i j : Fin 9, i.val < 2 → 2 ≤ j.val → j.val < 4 → |inner ℝ (y i) (y j)| ≤ 3 / 10
  · exact Or.inr ⟨h, hb, ht⟩
  · left
    push Not at ht
    obtain ⟨i, j, hi, hj2, hj4, hij⟩ := ht
    have hA0 := mval_zero_near h
    have hB0 := mval_one_near h
    have lA : ((Cell.m1 : ℤ) : ℝ) / 2000 ≤ mval y 0 := by
      rw [m1_eq]
      exact neg_one_le_mval h.unit (by norm_num)
    have lB : ((Cell.m1 : ℤ) : ℝ) / 2000 ≤ mval y 1 := by
      rw [m1_eq]
      exact neg_one_le_mval h.unit (by norm_num)
    by_cases hin : mval y 0 ≤ -(997 : ℝ) / 1000
    · obtain ⟨σ, hσ⟩ := sel_of_tilt h (d := 200)
        (ivl (a := Cell.m1) (b := Cell.cin) lA (by rw [cin_eq]; exact hin))
        (ivl (a := Cell.m1) (b := Cell.cin) lB (by rw [cin_eq]; linarith)) hi hj2 hj4
        (by push_cast; linarith)
      rcases hσ with hσ | hσ
      · exact ⟨σ, Cell.q2p, by decide, hσ⟩
      · exact ⟨σ, Cell.q2m, by decide, hσ⟩
    · rw [not_le] at hin
      obtain ⟨σ, hσ⟩ := sel_of_tilt h (d := 600)
        (ivl (a := Cell.cin) (b := Cell.a1) (by rw [cin_eq]; linarith) (by rw [a1_eq]; exact hA0))
        (ivl (a := Cell.m1) (b := Cell.a1) lB (by rw [a1_eq]; exact hB0)) hi hj2 hj4
        (by push_cast; linarith)
      rcases hσ with hσ | hσ
      · exact ⟨σ, Cell.q1p, by decide, hσ⟩
      · exact ⟨σ, Cell.q1m, by decide, hσ⟩

/-- **The cell L3-k2 before its core.** A chain with exactly two near pairs, both with an inner product of at most
`-99 / 100`, lies in one of the two pair claims of the ring split, or a relabelling of it lies in one of the four
selected-edge claims or in the core. -/
theorem l3k2_outer {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) (h0 : mval y 0 ≤ -(99 : ℝ) / 100) (h1 : mval y 1 ≤ -(99 : ℝ) / 100)
    (hf2 : -(9 : ℝ) / 10 < mval y 2) :
    (∃ c ∈ claimsRing, InPC c y)
      ∨ ∃ σ : Equiv.Perm (Fin 9), (∃ c ∈ claimsSel, InSC c (y ∘ σ)) ∨ Core (y ∘ σ) := by
  rcases ring_split hu hs hc h0 h1 hf2 with h | h
  · exact Or.inl h
  · right
    obtain ⟨σ, hσ, hb⟩ := exists_bent h
    rcases sel_or_core hσ hb with ⟨τ, c, hc', hin⟩ | hcore
    · refine ⟨σ * τ, Or.inl ⟨c, hc', ?_⟩⟩
      have e : y ∘ ⇑(σ * τ) = (y ∘ ⇑σ) ∘ ⇑τ := by
        rw [Equiv.Perm.coe_mul]
        rfl
      rw [e]
      exact hin
    · exact ⟨σ, Or.inr hcore⟩

/-- **The cell L3-k2 before its core, for the energy.** If the energy exceeds `35 / 2` on the pair claims of the
ring split and on the selected-edge claims, then it exceeds `35 / 2` for the chain, or a relabelling of the chain
lies in the core. -/
theorem l3k2_outer_energy (hR : Excl claimsRing) (hS : ExclSel claimsSel)
    {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) (h0 : mval y 0 ≤ -(99 : ℝ) / 100) (h1 : mval y 1 ≤ -(99 : ℝ) / 100)
    (hf2 : -(9 : ℝ) / 10 < mval y 2) :
    (35 : ℝ) / 2 < energyE y ∨ ∃ σ : Equiv.Perm (Fin 9), Core (y ∘ σ) := by
  rcases l3k2_outer hu hs hc h0 h1 hf2 with ⟨c, hc', hin⟩ | ⟨σ, ⟨c, hc', hin⟩ | hcore⟩
  · exact Or.inl (hR c hc' y hin)
  · left
    rw [← energyE_comp_perm y σ]
    exact hS c hc' _ hin
  · exact Or.inr ⟨σ, hcore⟩

/-- info: 'S3N9.l3k2_outer_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms l3k2_outer_energy

/-- info: 'S3N9.exclSel_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exclSel_of_cert

end S3N9
