module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import S3N9.Statement
public import S3N9.Separation

/-!
# The theorem for nine points: configurations in Euclidean space

The statement of the theorem (`S3N9/Statement.lean`) uses coordinates. The theorems of the certificates use
nine points of `EuclideanSpace ℝ (Fin 4)` and the energy `∑ i < j, 1 / ‖x i - x j‖ ^ 2`. This file relates the
two and contains the first analytic statements of the source.

* `energy_eq`, `onSphere_iff`, `injective_pt`: the bridge (row A2 of `S3N9/README.md`, first part);
* `energyE_comp_perm`: the energy does not depend on the labelling of the points;
* `exists_min_pair`: a pair of a set of labels with the smallest inner product;
* `Separated`, `separated_of_energy`: a configuration with energy at most `35 / 2` is separated
  (`lma:separation`, from the certificate of the row C1);
* `near_disjoint`: the near pairs of a separated configuration are disjoint (`lma:matching`, row A3).
-/

@[expose] public section

namespace S3N9

open Finset

/-- The harmonic energy of nine points of `ℝ⁴`, in the form of the theorems of the certificates. -/
noncomputable def energyE (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) : ℝ :=
  ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2

/-- The points of Euclidean space with the coordinates of a configuration. -/
noncomputable def pt (x : Fin 9 → Fin 4 → ℝ) (i : Fin 9) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 (x i)

theorem norm_pt_sub_sq (x : Fin 9 → Fin 4 → ℝ) (i j : Fin 9) :
    ‖pt x i - pt x j‖ ^ 2 = ∑ k, (x i k - x j k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

theorem norm_pt_sq (x : Fin 9 → Fin 4 → ℝ) (i : Fin 9) : ‖pt x i‖ ^ 2 = ∑ k, x i k ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

/-- The energy of the statement is the energy of the points of Euclidean space. -/
theorem energy_eq (x : Fin 9 → Fin 4 → ℝ) : energy x = energyE (pt x) := by
  unfold energy energyE
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_pt_sub_sq]

theorem norm_eq_one_iff_sq {E : Type*} [SeminormedAddCommGroup E] (v : E) : ‖v‖ = 1 ↔ ‖v‖ ^ 2 = 1 := by
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have h0 := norm_nonneg v
    nlinarith [sq_nonneg (‖v‖ - 1)]

theorem onSphere_iff (x : Fin 9 → Fin 4 → ℝ) : OnSphere x ↔ ∀ i, ‖pt x i‖ = 1 := by
  unfold OnSphere
  refine forall_congr' fun i => ?_
  rw [norm_eq_one_iff_sq, norm_pt_sq]

theorem injective_pt (x : Fin 9 → Fin 4 → ℝ) : Function.Injective (pt x) ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    exact h (by unfold pt; rw [hij])
  · intro h i j hij
    exact h (WithLp.toLp_injective 2 hij)

/-! ## The energy does not depend on the labelling -/

/-- A symmetric function of two labels that vanishes on the diagonal: the sum over all ordered pairs is twice the
sum over the pairs `i < j`. -/
theorem sum_all_eq (F : Fin 9 → Fin 9 → ℝ) (hsym : ∀ i j, F i j = F j i) (hd : ∀ i, F i i = 0) :
    ∑ i, ∑ j, F i j = 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
  have split : ∀ i : Fin 9, ∑ j, F i j
      = ∑ j ∈ univ.filter (fun j => i < j), F i j + ∑ j ∈ univ.filter (fun j => j < i), F i j := by
    intro i
    have h1 := Finset.sum_filter_add_sum_filter_not (univ : Finset (Fin 9)) (fun j => i < j) (fun j => F i j)
    have hset : univ.filter (fun j => ¬ i < j) = insert i (univ.filter (fun j => j < i)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, not_lt]
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact le_of_eq h
        · exact le_of_lt h
    have h2 : ∑ j ∈ univ.filter (fun j => ¬ i < j), F i j = ∑ j ∈ univ.filter (fun j => j < i), F i j := by
      rw [hset, Finset.sum_insert (by simp), hd, zero_add]
    rw [← h1, h2]
  have swap : ∑ i, ∑ j ∈ univ.filter (fun j => j < i), F i j
      = ∑ i, ∑ j ∈ univ.filter (fun j => i < j), F i j := by
    rw [Finset.sum_comm' (s' := fun j => univ.filter (fun i => j < i)) (t' := univ)]
    · exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hsym b a
    · intro a b
      simp
  rw [Finset.sum_congr rfl fun i _ => split i, Finset.sum_add_distrib, swap]
  ring

theorem energyE_eq_half (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) :
    energyE x = 1 / 2 * ∑ i, ∑ j, 1 / ‖x i - x j‖ ^ 2 := by
  rw [sum_all_eq (fun i j => 1 / ‖x i - x j‖ ^ 2) (fun i j => by rw [norm_sub_rev]) (fun i => by simp)]
  unfold energyE
  ring

/-- **The energy does not depend on the labelling of the points.** -/
theorem energyE_comp_perm (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (σ : Equiv.Perm (Fin 9)) :
    energyE (x ∘ σ) = energyE x := by
  rw [energyE_eq_half, energyE_eq_half]
  congr 1
  calc ∑ i, ∑ j, 1 / ‖x (σ i) - x (σ j)‖ ^ 2
      = ∑ i, ∑ j, 1 / ‖x (σ i) - x j‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => Equiv.sum_comp σ (fun j => 1 / ‖x (σ i) - x j‖ ^ 2)
    _ = ∑ i, ∑ j, 1 / ‖x i - x j‖ ^ 2 := Equiv.sum_comp σ (fun i => ∑ j, 1 / ‖x i - x j‖ ^ 2)

/-! ## Separated configurations and near pairs -/

/-- A pair of distinct labels of a set with at least two elements whose inner product is minimal among the pairs
of the set. -/
theorem exists_min_pair (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (S : Finset (Fin 9)) (hS : 1 < S.card) :
    ∃ i ∈ S, ∃ j ∈ S, i ≠ j ∧
      ∀ i' ∈ S, ∀ j' ∈ S, i' ≠ j' → inner ℝ (x i) (x j) ≤ inner ℝ (x i') (x j') := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hS
  have hne : ((S ×ˢ S).filter fun p : Fin 9 × Fin 9 => p.1 ≠ p.2).Nonempty :=
    ⟨(a, b), by simp [ha, hb, hab]⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p : Fin 9 × Fin 9 => inner ℝ (x p.1) (x p.2)) hne
  simp only [mem_filter, mem_product] at hp
  refine ⟨p.1, hp.1.1, p.2, hp.1.2, hp.2, fun i' hi' j' hj' hij' => ?_⟩
  exact hmin (i', j') (by simp [hi', hj', hij'])

/-- A configuration is separated if all inner products of distinct points are below `1089 / 2000`. -/
def Separated (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop :=
  ∀ i j, i ≠ j → inner ℝ (x i) (x j) < (1089 : ℝ) / 2000

/-- **A configuration with energy at most `35 / 2` is separated** (`lma:separation`). -/
theorem separated_of_energy {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖x i‖ = 1)
    (hx : Function.Injective x) (hE : energyE x ≤ 35 / 2) : Separated x :=
  fun _ _ hij => separation hu hx hE hij

/-- **The near pairs of a separated configuration are disjoint** (`lma:matching`): a point has an inner product
of at most `-9 / 10` with at most one other point. -/
theorem near_disjoint {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} (hu : ∀ i, ‖x i‖ = 1) (hs : Separated x)
    {i j l : Fin 9} (hjl : j ≠ l) (h1 : inner ℝ (x i) (x j) ≤ -(9 : ℝ) / 10)
    (h2 : inner ℝ (x i) (x l) ≤ -(9 : ℝ) / 10) : False := by
  have h0 : (0 : ℝ) ≤ ‖x j + (2 : ℝ) • x i + x l‖ ^ 2 := sq_nonneg _
  have hji : inner ℝ (x j) (x i) = inner ℝ (x i) (x j) := real_inner_comm _ _
  have hli : inner ℝ (x l) (x i) = inner ℝ (x i) (x l) := real_inner_comm _ _
  have hlj : inner ℝ (x l) (x j) = inner ℝ (x j) (x l) := real_inner_comm _ _
  have e : ‖x j + (2 : ℝ) • x i + x l‖ ^ 2
      = 6 + 4 * inner ℝ (x i) (x j) + 4 * inner ℝ (x i) (x l) + 2 * inner ℝ (x j) (x l) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hji, hli, hlj]
    simp only [real_inner_self_eq_norm_sq, hu, one_pow]
    ring
  have h3 := hs j l hjl
  rw [e] at h0
  linarith

/-- info: 'S3N9.near_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms near_disjoint

/-- info: 'S3N9.energyE_comp_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms energyE_comp_perm

end S3N9
