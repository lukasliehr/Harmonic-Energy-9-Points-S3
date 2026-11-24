module

public import S3N9.Chain
public import S3N9.Claims

/-!
# The theorem for nine points: from a chain to a pair claim

The cover lemmas of the source (`lma:celldomains`, `lma:coverK3`, `lma:coverK2`, `lma:coverK1`, `lma:coverRING`)
assign a pair claim to a configuration by the values of its canonical minima. For a chain labelling the classes
of all these claims are the first pairs of the chain, so each of them is an instance of one statement.

* `pairClaim_of_chain`: a chain with `k` near pairs lies in the pair claim with `p ≥ k` classes of two points
  whose intervals contain the inner products of the first `p` pairs of the chain, and whose bound `ℓ` for the
  last class is at most the inner product of the next pair of the chain (row A4 of `S3N9/README.md`, first part).
-/

@[expose] public section

namespace S3N9

open Finset

/-- **A chain lies in a pair claim.** -/
theorem pairClaim_of_chain {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) {k p : ℕ} (hkp : k ≤ p) (hp : p ≤ 4)
    (hnear : ∀ c < k, ∀ a b : Fin 9, a.val = 2 * c → b.val = 2 * c + 1 → inner ℝ (y a) (y b) ≤ -(9 : ℝ) / 10)
    (hfar : k < 4 → ∀ a b : Fin 9, a.val = 2 * k → b.val = 2 * k + 1 → -(9 : ℝ) / 10 < inner ℝ (y a) (y b))
    {I : ℕ → ℝ × ℝ} {ℓ : ℝ}
    (hI : ∀ c < p, ∀ a b : Fin 9, a.val = 2 * c → b.val = 2 * c + 1 →
      (I c).1 ≤ inner ℝ (y a) (y b) ∧ inner ℝ (y a) (y b) ≤ (I c).2)
    (hℓ : p < 4 → ∀ a b : Fin 9, a.val = 2 * p → b.val = 2 * p + 1 → ℓ ≤ inner ℝ (y a) (y b)) :
    InPairClaim p I ℓ y where
  unit := hu
  pair := fun m n hmn hcls hlt => by
    have hval : m.val ≠ n.val := fun h => hmn (Fin.ext h)
    have hm : m.val < 2 * p := by
      by_contra h
      unfold clsP at hlt
      rw [if_neg h] at hlt
      exact lt_irrefl _ hlt
    have em : clsP p m = m.val / 2 := by
      unfold clsP
      rw [if_pos hm]
    have hn : n.val < 2 * p := by
      by_contra h
      rw [em] at hcls
      unfold clsP at hcls
      rw [if_neg h] at hcls
      omega
    have en : clsP p n = n.val / 2 := by
      unfold clsP
      rw [if_pos hn]
    rw [em, en] at hcls
    rw [em]
    by_cases hpar : m.val % 2 = 0
    · exact hI (m.val / 2) (by omega) m n (by omega) (by omega)
    · rw [real_inner_comm]
      exact hI (m.val / 2) (by omega) n m (by omega) (by omega)
  rest := fun m n hmn hm hn => by
    have a1 := clsP_eq_last hm
    have a2 := clsP_eq_last hn
    have hval : m.val ≠ n.val := fun h => hmn (Fin.ext h)
    have hp4 : p < 4 := by
      have h1 := m.isLt
      have h2 := n.isLt
      omega
    obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * p := ⟨⟨2 * p, by omega⟩, rfl⟩
    obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * p + 1 := ⟨⟨2 * p + 1, by omega⟩, rfl⟩
    exact le_trans (hℓ hp4 a b ha hb) (hc p hp4 a b ha hb m n a1 a2 hmn)
  low := fun m n hmn hcls => by
    refine le_of_lt (chain_far hu hs hc (le_trans hkp hp) hnear hfar hmn (Or.inl ?_))
    intro h
    apply hcls
    unfold clsP
    split_ifs <;> omega
  high := fun m n hmn => le_of_lt (hs m n hmn)

/-- info: 'S3N9.pairClaim_of_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairClaim_of_chain

end S3N9
