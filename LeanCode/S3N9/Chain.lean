module

public import S3N9.Basic

/-!
# The theorem for nine points: chain labellings

The canonical minima of the source (`def:canonical`) are a first pair with the smallest inner product, a second
pair with the smallest inner product among the pairs disjoint from the first, and so on. We express them by a
labelling: a labelled configuration `y` is a *chain* up to `k` if for every `c < k` the pair of the positions
`2 c`, `2 c + 1` has the smallest inner product among all pairs of positions from `2 c` on. No rule for ties is
needed.

* `exists_perm_front`: a permutation that fixes the positions below `s` and brings two given positions to `s`
  and `s + 1`;
* `exists_chain`: every configuration has a chain labelling up to `4` (row A3 of `S3N9/README.md`);
* `chain_far`: the near pairs of a separated configuration are the first pairs of a chain (`lma:kchar`).
-/

@[expose] public section

namespace S3N9

open Finset

/-- A permutation of the positions that fixes the positions below `s` and maps the positions `s` and `s + 1` to
two given distinct positions from `s` on. -/
theorem exists_perm_front {s : ℕ} {a b i j : Fin 9} (ha : a.val = s) (hb : b.val = s + 1) (hi : s ≤ i.val)
    (hj : s ≤ j.val) (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin 9), τ a = i ∧ τ b = j ∧ ∀ m : Fin 9, m.val < s → τ m = m := by
  have hab : a ≠ b := fun h => by
    have := congrArg Fin.val h
    omega
  have haj : a ≠ Equiv.swap a i j := by
    intro h
    apply hij
    have h' := congrArg (Equiv.swap a i) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h'
    exact h'
  have hjs : s ≤ (Equiv.swap a i j).val := by
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · exact hi
    · exact le_of_eq ha.symm
    · exact hj
  refine ⟨Equiv.swap a i * Equiv.swap b (Equiv.swap a i j), ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hab haj, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]
  · intro m hm
    have h1 : m ≠ b := fun h => by
      have := congrArg Fin.val h
      omega
    have h2 : m ≠ Equiv.swap a i j := fun h => by
      have := congrArg Fin.val h
      omega
    have h3 : m ≠ a := fun h => by
      have := congrArg Fin.val h
      omega
    have h4 : m ≠ i := fun h => by
      have := congrArg Fin.val h
      omega
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- A labelled configuration is a chain up to `k`: for `c < k` the pair of the positions `2 c`, `2 c + 1` has the
smallest inner product among the pairs of positions from `2 c` on. -/
def IsChain (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) (k : ℕ) : Prop :=
  ∀ c < k, ∀ a b : Fin 9, a.val = 2 * c → b.val = 2 * c + 1 → ∀ m n : Fin 9, 2 * c ≤ m.val → 2 * c ≤ n.val →
    m ≠ n → inner ℝ (y a) (y b) ≤ inner ℝ (y m) (y n)

/-- **Every configuration has a chain labelling** (the canonical minima, `def:canonical`). -/
theorem exists_chain (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) :
    ∀ k ≤ 4, ∃ σ : Equiv.Perm (Fin 9), IsChain (x ∘ σ) k
  | 0, _ => ⟨1, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
  | k + 1, hk => by
    obtain ⟨σ, hσ⟩ := exists_chain x k (by omega)
    have hk3 : k ≤ 3 := by omega
    have hcard : 1 < (univ.filter fun m : Fin 9 => 2 * k ≤ m.val).card := by
      interval_cases k <;> decide
    obtain ⟨i, hi, j, hj, hij, hmin⟩ := exists_min_pair (x ∘ σ) _ hcard
    simp only [mem_filter, mem_univ, true_and] at hi hj
    obtain ⟨pa, hpa⟩ : ∃ p : Fin 9, p.val = 2 * k := ⟨⟨2 * k, by omega⟩, rfl⟩
    obtain ⟨pb, hpb⟩ : ∃ p : Fin 9, p.val = 2 * k + 1 := ⟨⟨2 * k + 1, by omega⟩, rfl⟩
    obtain ⟨τ, hτa, hτb, hτfix⟩ := exists_perm_front hpa hpb hi hj hij
    have hτge : ∀ m : Fin 9, 2 * k ≤ m.val → 2 * k ≤ (τ m).val := by
      intro m hm
      by_contra hlt
      have h1 := hτfix (τ m) (not_le.1 hlt)
      have h2 := τ.injective h1
      rw [h2] at hlt
      exact hlt hm
    refine ⟨σ * τ, fun c hc a b ha hb m n hm hn hmn => ?_⟩
    show inner ℝ (x (σ (τ a))) (x (σ (τ b))) ≤ inner ℝ (x (σ (τ m))) (x (σ (τ n)))
    have hne : τ m ≠ τ n := fun h => hmn (τ.injective h)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | hck
    · rw [hτfix a (by omega), hτfix b (by omega)]
      have hm' : 2 * c ≤ (τ m).val := by
        by_cases h : m.val < 2 * k
        · rw [hτfix m h]
          exact hm
        · have := hτge m (not_lt.1 h)
          omega
      have hn' : 2 * c ≤ (τ n).val := by
        by_cases h : n.val < 2 * k
        · rw [hτfix n h]
          exact hn
        · have := hτge n (not_lt.1 h)
          omega
      exact hσ c hlt a b ha hb (τ m) (τ n) hm' hn' hne
    · have ea : a = pa := Fin.ext (by omega)
      have eb : b = pb := Fin.ext (by omega)
      rw [ea, eb, hτa, hτb]
      rw [hck] at hm hn
      exact hmin (τ m) (by simp only [mem_filter, mem_univ, true_and]; exact hτge m hm) (τ n)
        (by simp only [mem_filter, mem_univ, true_and]; exact hτge n hn) hne

/-- **The near pairs of a chain** (`lma:kchar`). Let the first `k` pairs of a chain of a separated configuration be
near, and let the next pair of the chain not be near. Then every other pair of positions has an inner product
above `-9 / 10`: the near pairs are the first `k` pairs of the chain. -/
theorem chain_far {y : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖y i‖ = 1) (hs : Separated y)
    (hc : IsChain y 4) {k : ℕ} (hk : k ≤ 4)
    (hnear : ∀ c < k, ∀ a b : Fin 9, a.val = 2 * c → b.val = 2 * c + 1 → inner ℝ (y a) (y b) ≤ -(9 : ℝ) / 10)
    (hfar : k < 4 → ∀ a b : Fin 9, a.val = 2 * k → b.val = 2 * k + 1 → -(9 : ℝ) / 10 < inner ℝ (y a) (y b))
    {m n : Fin 9} (hmn : m ≠ n) (hnp : m.val / 2 ≠ n.val / 2 ∨ 2 * k ≤ m.val) :
    -(9 : ℝ) / 10 < inner ℝ (y m) (y n) := by
  have hval : m.val ≠ n.val := fun h => hmn (Fin.ext h)
  have key : ∀ p q : Fin 9, p ≠ q → p.val < 2 * k → p.val / 2 ≠ q.val / 2 →
      -(9 : ℝ) / 10 < inner ℝ (y p) (y q) := by
    intro p q hpq hp hdiv
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨p', hp'⟩ : ∃ r : Fin 9, r.val = if p.val % 2 = 0 then p.val + 1 else p.val - 1 :=
      ⟨⟨if p.val % 2 = 0 then p.val + 1 else p.val - 1, by split_ifs <;> omega⟩, rfl⟩
    have hp'q : p' ≠ q := fun h => by
      have h' := congrArg Fin.val h
      rw [hp'] at h'
      split_ifs at h' <;> omega
    have hnr : inner ℝ (y p) (y p') ≤ -(9 : ℝ) / 10 := by
      by_cases hpar : p.val % 2 = 0
      · rw [if_pos hpar] at hp'
        exact hnear (p.val / 2) (by omega) p p' (by omega) (by omega)
      · rw [if_neg hpar] at hp'
        rw [real_inner_comm]
        exact hnear (p.val / 2) (by omega) p' p (by omega) (by omega)
    exact near_disjoint hu hs hp'q hnr hle
  by_cases hm : m.val < 2 * k
  · rcases hnp with h | h
    · exact key m n hmn hm h
    · omega
  · by_cases hn : n.val < 2 * k
    · rw [real_inner_comm]
      exact key n m (Ne.symm hmn) hn (by omega)
    · have hk4 : k < 4 := by
        have h1 := m.isLt
        have h2 := n.isLt
        omega
      obtain ⟨a, ha⟩ : ∃ r : Fin 9, r.val = 2 * k := ⟨⟨2 * k, by omega⟩, rfl⟩
      obtain ⟨b, hb⟩ : ∃ r : Fin 9, r.val = 2 * k + 1 := ⟨⟨2 * k + 1, by omega⟩, rfl⟩
      exact lt_of_lt_of_le (hfar hk4 a b ha hb) (hc k hk4 a b ha hb m n (by omega) (by omega) hmn)

/-- info: 'S3N9.exists_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_chain

end S3N9
