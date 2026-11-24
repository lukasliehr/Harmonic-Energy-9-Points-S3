module

public import S3N9.Basic
public import CAP.Wsos.Claims

/-!
# The theorem for nine points: pair claims

A *pair claim* `P(I₀, …, I_{p-1}; ℓ)` of the source (Section 4.2) has `p ≤ 4` classes of two points and one class
with the remaining `9 - 2 p` points. The inner product of the two points of the class `c < p` lies in `I c`, the
inner products inside the last class are at least `ℓ`, all other inner products are at least `-9 / 10`, and all
inner products of distinct points are at most `1089 / 2000`.

We state a claim for a *labelled* configuration `y`: the positions `2 c` and `2 c + 1` carry the class `c < p`,
and the positions from `2 p` on carry the last class (`clsP`). A configuration `x` admits a labelling into the
claim if `x ∘ σ` lies in it for a permutation `σ`; the energy does not change (`energyE_comp_perm`).

* `InPairClaim`: a labelled configuration in a pair claim;
* `inClaim_of_pairClaim`: it satisfies the hypothesis `CAP.Wsos.InClaim` of the theorem of a typed certificate
  whose claim has the classes and contains the intervals of the pair claim (row A5 of `S3N9/README.md`);
* `inClaim_of_one`: the same for the claim of the cell L0, which has one class of nine points.
-/

@[expose] public section

namespace S3N9

open Finset CAP.Wsos

/-- The class of a position in a pair claim with `p` pairs. -/
def clsP (p : ℕ) (m : Fin 9) : ℕ := if m.val < 2 * p then m.val / 2 else p

theorem clsP_le (p : ℕ) (m : Fin 9) : clsP p m ≤ p := by
  unfold clsP
  split_ifs with h
  · omega
  · exact le_rfl

theorem clsP_eq_last {p : ℕ} {m : Fin 9} (h : clsP p m = p) : 2 * p ≤ m.val := by
  unfold clsP at h
  split_ifs at h with h1
  · omega
  · omega

/-- The classes of a pair claim have the sizes `2, …, 2, 9 - 2 p`. -/
theorem card_clsP {p : ℕ} (hp : p ≤ 4) {c : ℕ} (hc : c ≤ p) :
    (univ.filter fun k : Fin 9 => clsP p k = c).card = if c < p then 2 else 9 - 2 * p := by
  interval_cases p <;> interval_cases c <;> decide

/-- A labelled configuration in the pair claim `P(I₀, …, I_{p-1}; ℓ)`. -/
structure InPairClaim (p : ℕ) (I : ℕ → ℝ × ℝ) (ℓ : ℝ) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop where
  unit : ∀ m, ‖y m‖ = 1
  pair : ∀ m n : Fin 9, m ≠ n → clsP p m = clsP p n → clsP p m < p →
    (I (clsP p m)).1 ≤ inner ℝ (y m) (y n) ∧ inner ℝ (y m) (y n) ≤ (I (clsP p m)).2
  rest : ∀ m n : Fin 9, m ≠ n → clsP p m = p → clsP p n = p → ℓ ≤ inner ℝ (y m) (y n)
  low : ∀ m n : Fin 9, m ≠ n → clsP p m ≠ clsP p n → -(9 : ℝ) / 10 ≤ inner ℝ (y m) (y n)
  high : ∀ m n : Fin 9, m ≠ n → inner ℝ (y m) (y n) ≤ (1089 : ℝ) / 2000

/-- **A pair claim gives the hypothesis of a typed certificate.** Let the certificate have the `p + 1` classes of
the pair claim, and let the intervals `K` of its claim contain those of the pair claim. Then a labelled
configuration in the pair claim satisfies `CAP.Wsos.InClaim`. -/
theorem inClaim_of_pairClaim {p q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {I : ℕ → ℝ × ℝ} {ℓ : ℝ}
    {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hp : p ≤ 4) (hq : q = p + 1) (hn : ∀ c < p, C.n c = 2)
    (hnr : C.n p = 9 - 2 * p)
    (hdiag : ∀ c < p, (K c c).lo ≤ (I c).1 ∧ (I c).2 ≤ (K c c).hi)
    (hrest : p < 4 → (K p p).lo ≤ ℓ ∧ (1089 : ℝ) / 2000 ≤ (K p p).hi)
    (hoff : ∀ c1 c2, c1 < c2 → c2 ≤ p → (K c1 c2).lo ≤ -(9 : ℝ) / 10 ∧ (1089 : ℝ) / 2000 ≤ (K c1 c2).hi)
    (h : InPairClaim p I ℓ y) : InClaim q C K (clsP p) y where
  lab :=
    { lt := fun m => by
        rw [hq]
        exact Nat.lt_succ_of_le (clsP_le p m)
      card := fun c hc => by
        rw [hq] at hc
        rw [card_clsP hp (Nat.lt_succ_iff.1 hc)]
        split_ifs with h1
        · exact (hn c h1).symm
        · have : c = p := by omega
          rw [this, hnr] }
  unit := h.unit
  iv := fun m n hmn hle => by
    rcases Nat.lt_or_ge (clsP p m) (clsP p n) with hlt | hge
    · have h1 := hoff _ _ hlt (clsP_le p n)
      exact ⟨le_trans h1.1 (h.low m n hmn (ne_of_lt hlt)), le_trans (h.high m n hmn) h1.2⟩
    · have heq : clsP p n = clsP p m := le_antisymm hge hle
      rw [heq]
      by_cases hc : clsP p m < p
      · have h1 := hdiag _ hc
        have h2 := h.pair m n hmn heq.symm hc
        exact ⟨le_trans h1.1 h2.1, le_trans h2.2 h1.2⟩
      · have hm : clsP p m = p := le_antisymm (clsP_le p m) (not_lt.1 hc)
        have hn' : clsP p n = p := by rw [heq, hm]
        have h4 : p < 4 := by
          have a := clsP_eq_last hm
          have b := clsP_eq_last hn'
          have hne : m.val ≠ n.val := fun e => hmn (Fin.ext e)
          omega
        have h1 := hrest h4
        rw [hm]
        exact ⟨le_trans h1.1 (h.rest m n hmn hm hn'), le_trans (h.high m n hmn) h1.2⟩

/-- **The claim of the cell L0**: one class of nine points whose inner products are at least `l`. It gives the
hypothesis of a certificate with one class whose interval contains `[l, 1089 / 2000]`. -/
theorem inClaim_of_one {q : ℕ} {C : Cert} {K : ℕ → ℕ → Ival} {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} {l : ℝ}
    (hq : q = 1) (hn : C.n 0 = 9) (hK : (K 0 0).lo ≤ l ∧ (1089 : ℝ) / 2000 ≤ (K 0 0).hi) (hu : ∀ i, ‖y i‖ = 1)
    (hs : Separated y) (hl : ∀ m n : Fin 9, m ≠ n → l ≤ inner ℝ (y m) (y n)) :
    InClaim q C K (fun _ : Fin 9 => 0) y where
  lab :=
    { lt := fun _ => by
        rw [hq]
        norm_num
      card := fun x hx => by
        have h0 : x = 0 := by omega
        subst h0
        simp [hn] }
  unit := hu
  iv := fun m n hmn _ => ⟨le_trans hK.1 (hl m n hmn), le_trans (le_of_lt (hs m n hmn)) hK.2⟩

/-- info: 'S3N9.inClaim_of_pairClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms inClaim_of_pairClaim

end S3N9
