module

public import S3N9.Cells

/-!
# The theorem for nine points: a claim of a certificate contains a claim of the paper

The theorem `energy_claim<k>` of a typed certificate has the hypothesis `CAP.Wsos.InClaim q C K cls x` for the
classes `C.n` and the intervals `K` of a claim of the certificate. The statements `pcFits` and `oneFits` say that
these classes and intervals are those of a pair claim of the paper, or of the claim of the cell L0, and that the
intervals of the certificate contain those of the paper. They are comparisons of integers, which the kernel decides
for the data of a certificate.

* `inClaim_of_PC`, `inClaim_of_L0`: a labelled configuration in the claim of the paper satisfies the hypothesis of
  the certificate (row A5 of `S3N9/README.md`).
* `Excl l`, `ExclL0`: the energy exceeds `35 / 2` on every pair claim of the list `l`, and on the claim of the cell
  L0. `excl_of_cert` and `exclL0_of_cert` derive them from the theorem of a claim of a certificate; the module
  that applies them to the certificates is generated (`certgen/s3n9_cells.py`) and compiled by a driver.
-/

@[expose] public section

namespace S3N9

open CAP.Wsos

/-- The interval `v` of a claim of a certificate contains `[a / 2000, b / 2000]`. -/
def ivalFits (v : Ival) (a b : ℤ) : Prop :=
  0 < v.ld ∧ 0 < v.hd ∧ ((v.lp : ℤ) - v.ln) * 2000 ≤ a * v.ld ∧ b * v.hd ≤ ((v.hp : ℤ) - v.hn) * 2000

instance (v : Ival) (a b : ℤ) : Decidable (ivalFits v a b) := by
  unfold ivalFits
  infer_instance

theorem ivalFits_real {v : Ival} {a b : ℤ} (h : ivalFits v a b) :
    v.lo ≤ (a : ℝ) / 2000 ∧ (b : ℝ) / 2000 ≤ v.hi := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have d1 : (0 : ℝ) < v.ld := by exact_mod_cast h1
  have d2 : (0 : ℝ) < v.hd := by exact_mod_cast h2
  have e3 : ((v.lp : ℝ) - v.ln) * 2000 ≤ a * v.ld := by exact_mod_cast h3
  have e4 : (b : ℝ) * v.hd ≤ ((v.hp : ℝ) - v.hn) * 2000 := by exact_mod_cast h4
  constructor
  · unfold Ival.lo
    rw [div_le_div_iff₀ d1 (by norm_num)]
    exact e3
  · unfold Ival.hi
    rw [div_le_div_iff₀ (by norm_num) d2]
    exact e4

/-- The claim `K` of a certificate with the classes `C.n` has the classes of the pair claim `c` and contains its
intervals. -/
def pcFits (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) (c : PC) : Prop :=
  c.I.length ≤ 4 ∧ q = c.I.length + 1 ∧ (∀ i < c.I.length, C.n i = 2) ∧ C.n c.I.length = 9 - 2 * c.I.length
    ∧ (∀ i < c.I.length, ivalFits (K i i) (c.I.getD i (0, 0)).1 (c.I.getD i (0, 0)).2)
    ∧ (c.I.length < 4 → ivalFits (K c.I.length c.I.length) c.l 1089)
    ∧ ∀ c2 < c.I.length + 1, ∀ c1 < c2, ivalFits (K c1 c2) (-1800) 1089

instance (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) (c : PC) : Decidable (pcFits q C K c) := by
  unfold pcFits
  infer_instance

/-- **A pair claim of the paper in a claim of a certificate.** -/
theorem inClaim_of_PC {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {c : PC} {y : Fin 9 → EuclideanSpace ℝ (Fin 4)}
    (hf : pcFits q C K c) (h : InPC c y) : InClaim q C K (clsP c.I.length) y := by
  obtain ⟨hp, hq, hn, hnr, hd, hr, ho⟩ := hf
  refine inClaim_of_pairClaim hp hq hn hnr (fun i hi => ivalFits_real (hd i hi)) (fun h4 => ?_)
    (fun c1 c2 h12 h2 => ?_) h
  · have h1 := ivalFits_real (hr h4)
    refine ⟨h1.1, ?_⟩
    have h2 := h1.2
    push_cast at h2
    exact h2
  · have h1 := ivalFits_real (ho c2 (Nat.lt_succ_of_le h2) c1 h12)
    obtain ⟨h3, h4⟩ := h1
    push_cast at h3 h4
    constructor
    · linarith
    · exact h4

/-- The claim `K` of a certificate with one class of nine points contains the claim of the cell L0. -/
def oneFits (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) : Prop :=
  q = 1 ∧ C.n 0 = 9 ∧ ivalFits (K 0 0) (-1805) 1089

instance (q : ℕ) (C : Cert) (K : ℕ → ℕ → Ival) : Decidable (oneFits q C K) := by
  unfold oneFits
  infer_instance

/-- **The claim of the cell L0 in the claim of a certificate with one class.** -/
theorem inClaim_of_L0 {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {y : Fin 9 → EuclideanSpace ℝ (Fin 4)}
    (hf : oneFits q C K) (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hl : ∀ m n : Fin 9, m ≠ n → -(361 : ℝ) / 400 ≤ inner ℝ (y m) (y n)) :
    InClaim q C K (fun _ : Fin 9 => 0) y := by
  obtain ⟨hq, hn, hK⟩ := hf
  have h1 := ivalFits_real hK
  obtain ⟨h3, h4⟩ := h1
  push_cast at h3 h4
  exact inClaim_of_one (l := -(361 : ℝ) / 400) hq hn ⟨by linarith, h4⟩ hu hs hl

/-- The energy exceeds `35 / 2` on every pair claim of the list `l`. -/
def Excl (l : List PC) : Prop :=
  ∀ c ∈ l, ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InPC c y → (35 : ℝ) / 2 < energyE y

theorem excl_nil : Excl [] := fun _ hc => absurd hc List.not_mem_nil

theorem excl_cons {a : PC} {l : List PC}
    (ha : ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InPC a y → (35 : ℝ) / 2 < energyE y) (hl : Excl l) :
    Excl (a :: l) := by
  intro c hc y hy
  rcases List.mem_cons.1 hc with rfl | h
  · exact ha y hy
  · exact hl c h y hy

/-- **The theorem of a claim of a certificate excludes a pair claim of the paper**: `hE` is the theorem
`energy_claim<k>` of a typed certificate, `hf` the comparison of its claim with the pair claim `c`. -/
theorem excl_of_cert {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {c : PC} (hf : pcFits q C K c)
    (hE : ∀ {cls : Fin 9 → ℕ} {x : Fin 9 → EuclideanSpace ℝ (Fin 4)}, InClaim q C K cls x →
      (35 : ℝ) / 2 < ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2) :
    ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), InPC c y → (35 : ℝ) / 2 < energyE y :=
  fun _ h => hE (inClaim_of_PC hf h)

/-- The energy exceeds `35 / 2` on the claim of the cell L0: no pair of points has an inner product below
`-361 / 400`. -/
def ExclL0 : Prop :=
  ∀ y : Fin 9 → EuclideanSpace ℝ (Fin 4), (∀ i, ‖y i‖ = 1) → Separated y →
    (∀ m n : Fin 9, m ≠ n → -(361 : ℝ) / 400 ≤ inner ℝ (y m) (y n)) → (35 : ℝ) / 2 < energyE y

/-- **The theorem of the untyped certificate excludes the cell L0.** -/
theorem exclL0_of_cert {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} (hf : oneFits q C K)
    (hE : ∀ {cls : Fin 9 → ℕ} {x : Fin 9 → EuclideanSpace ℝ (Fin 4)}, InClaim q C K cls x →
      (35 : ℝ) / 2 < ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2) : ExclL0 :=
  fun _ hu hs hl => hE (inClaim_of_L0 hf hu hs hl)

/-- info: 'S3N9.excl_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms excl_of_cert

/-- info: 'S3N9.exclL0_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exclL0_of_cert

end S3N9
