module

public import S3N9.Minimum
public import S3N9.Cstar

/-!
# The theorem for nine points: the case of equality and the theorem

`congruent_of_contacts` (`lma:pentagon`, `prop:equality`; rows A2 and A10 of `S3N9/README.md`): a configuration
of nine distinct points of the unit sphere whose relabelling has the contacts (`S3N9.Contacts`) arises from `Cstar`
by an orthogonal map and a relabelling. The proof: the pairs `A` and `B` are antipodal and orthogonal, so with a
ring point they form an orthonormal family, which we extend to an orthonormal basis `b`. A ring point lies in the
plane of `b 0`, `b 1`, its first coordinate is a root of `4 t² + 2 t - 1`, hence `cos 72°` or `cos 144°`, and its
second coordinate has the square `1 - t²`: it is one of the four other vertices of the regular pentagon with the
vertex `b 0`. Distinct ring points are distinct vertices. The matrix of `b` in the standard basis is orthogonal and
maps the points of `Cstar` to the points of the configuration.

`harmonic9_of` (row A11): the theorem `S3N9.Harmonic9`, given the six statements of the certificates.
-/

@[expose] public section

namespace S3N9

open Real

/-- The roots of `4 t² + 2 t - 1` are `cos 72°` and `cos 144°`. -/
theorem root_cases {t : ℝ} (h : 4 * t ^ 2 + 2 * t - 1 = 0) : t = cPlus ∨ t = cMinus := by
  have e : 4 * (t - cPlus) * (t - cMinus) = 4 * t ^ 2 + 2 * t - 1 := by
    unfold cPlus cMinus
    linear_combination (-1 / 4) * sqrt5_sq
  rw [h] at e
  rcases mul_eq_zero.1 e with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · norm_num at h2
    · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- A point `(a, β)` of the unit circle with `a = cos 72°` or `a = cos 144°` is a vertex `m = 1, …, 4` of the
regular pentagon. -/
theorem vertex_of {a β : ℝ} (ha : a = cPlus ∨ a = cMinus) (h1 : a ^ 2 + β ^ 2 = 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ 4 ∧ a = cos (2 * π * m / 5) ∧ β = sin (2 * π * m / 5) := by
  have ang : ∀ m : ℕ, 2 * π * (m : ℝ) / 5 = (m : ℝ) * (2 * π / 5) := fun m => by ring
  have c1 : cos (2 * π * ((1 : ℕ) : ℝ) / 5) = cPlus := by
    rw [ang, cos_d 1 le_rfl (by norm_num)]
    simp [cP]
  have c2 : cos (2 * π * ((2 : ℕ) : ℝ) / 5) = cMinus := by
    rw [ang, cos_d 2 (by norm_num) (by norm_num)]
    simp [cP]
  have c3 : cos (2 * π * ((3 : ℕ) : ℝ) / 5) = cMinus := by
    rw [ang, cos_d 3 (by norm_num) (by norm_num)]
    simp [cP]
  have c4 : cos (2 * π * ((4 : ℕ) : ℝ) / 5) = cPlus := by
    rw [ang, cos_d 4 (by norm_num) le_rfl]
    simp [cP]
  have s3 : sin (2 * π * ((3 : ℕ) : ℝ) / 5) = -sin (2 * π * ((2 : ℕ) : ℝ) / 5) := by
    rw [← Real.sin_two_pi_sub]
    congr 1
    push_cast
    ring
  have s4 : sin (2 * π * ((4 : ℕ) : ℝ) / 5) = -sin (2 * π * ((1 : ℕ) : ℝ) / 5) := by
    rw [← Real.sin_two_pi_sub]
    congr 1
    push_cast
    ring
  rcases ha with ha | ha
  · have hb : β ^ 2 = sin (2 * π * ((1 : ℕ) : ℝ) / 5) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (2 * π * ((1 : ℕ) : ℝ) / 5)
      rw [c1] at this
      rw [ha] at h1
      linarith
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hb with hβ | hβ
    · exact ⟨1, le_rfl, by norm_num, by rw [c1]; exact ha, hβ⟩
    · exact ⟨4, by norm_num, le_rfl, by rw [c4]; exact ha, by rw [s4]; exact hβ⟩
  · have hb : β ^ 2 = sin (2 * π * ((2 : ℕ) : ℝ) / 5) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (2 * π * ((2 : ℕ) : ℝ) / 5)
      rw [c2] at this
      rw [ha] at h1
      linarith
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hb with hβ | hβ
    · exact ⟨2, by norm_num, by norm_num, by rw [c2]; exact ha, hβ⟩
    · exact ⟨3, by norm_num, by norm_num, by rw [c3]; exact ha, by rw [s3]; exact hβ⟩

/-- **Rigidity** (`lma:pentagon`, `prop:equality`). A configuration of nine distinct points of the unit sphere
with a relabelling that has the contacts arises from `Cstar` by an orthogonal map and a relabelling. -/
theorem congruent_of_contacts {x : Fin 9 → Fin 4 → ℝ} (hx : OnSphere x) (hinj : Function.Injective x)
    {μ : Equiv.Perm (Fin 9)} (hK : Contacts (pt x ∘ μ)) : Congruent Cstar x := by
  obtain ⟨z, hz⟩ : ∃ z : Fin 9 → EuclideanSpace ℝ (Fin 4), z = pt x ∘ μ := ⟨_, rfl⟩
  rw [← hz] at hK
  have hu : ∀ p, ‖z p‖ = 1 := fun p => by
    rw [hz]
    exact (onSphere_iff x).1 hx (μ p)
  have hzinj : Function.Injective z := by
    rw [hz]
    exact ((injective_pt x).2 hinj).comp μ.injective
  obtain ⟨k01, k23, kAB, kAR, kRR⟩ := hK
  have hself : ∀ p, inner ℝ (z p) (z p) = 1 := fun p => by
    rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have neg_of : ∀ p q : Fin 9, inner ℝ (z p) (z q) = -1 → z q = -z p := by
    intro p q h
    have h1 : ‖z p + z q‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hu, hu, h]
      ring
    have h0 : z p + z q = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
    exact eq_neg_of_add_eq_zero_right h0
  have e1 : z 1 = -z 0 := neg_of 0 1 k01
  have e3 : z 3 = -z 2 := neg_of 2 3 k23
  have h02 : inner ℝ (z 0) (z 2) = 0 := kAB 0 2 (by decide) (by decide) (by decide)
  have h20 : inner ℝ (z 2) (z 0) = 0 := by rw [real_inner_comm, h02]
  have h04 : inner ℝ (z 0) (z 4) = 0 := kAR 0 4 (by decide) (by decide)
  have h40 : inner ℝ (z 4) (z 0) = 0 := by rw [real_inner_comm, h04]
  have h24 : inner ℝ (z 2) (z 4) = 0 := kAR 2 4 (by decide) (by decide)
  have h42 : inner ℝ (z 4) (z 2) = 0 := by rw [real_inner_comm, h24]
  -- an orthonormal basis with `b 0 = z 4`, `b 2 = z 0`, `b 3 = z 2`
  have hv : Orthonormal ℝ (({0, 2, 3} : Set (Fin 4)).domRestrict ![z 4, 0, z 0, z 2]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
      simp [Set.domRestrict, hu, h02, h20, h04, h40, h24, h42]
  obtain ⟨b, hb'⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have b0 : b 0 = z 4 := hb' 0 (by simp)
  have b2 : b 2 = z 0 := hb' 2 (by simp)
  have b3 : b 3 = z 2 := hb' 3 (by simp)
  have hon := orthonormal_iff_ite.mp b.orthonormal
  have b00 : inner ℝ (b 0) (b 0) = 1 := by simpa using hon 0 0
  have b11 : inner ℝ (b 1) (b 1) = 1 := by simpa using hon 1 1
  have b01 : inner ℝ (b 0) (b 1) = 0 := by simpa using hon 0 1
  have b10 : inner ℝ (b 1) (b 0) = 0 := by simpa using hon 1 0
  -- a ring point in the plane of `b 0`, `b 1`
  have expand : ∀ p : Fin 9, 4 ≤ p.val →
      z p = inner ℝ (b 0) (z p) • b 0 + inner ℝ (b 1) (z p) • b 1 := by
    intro p hp
    have h := b.sum_repr' (z p)
    rw [Fin.sum_univ_four] at h
    have a2 : inner ℝ (b 2) (z p) = 0 := by
      rw [b2]
      exact kAR 0 p (by decide) hp
    have a3 : inner ℝ (b 3) (z p) = 0 := by
      rw [b3]
      exact kAR 2 p (by decide) hp
    rw [a2, a3, zero_smul, zero_smul, add_zero, add_zero] at h
    exact h.symm
  have unit2 : ∀ p : Fin 9, 4 ≤ p.val → inner ℝ (b 0) (z p) ^ 2 + inner ℝ (b 1) (z p) ^ 2 = 1 := by
    intro p hp
    have h := hself p
    nth_rewrite 1 [expand p hp] at h
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left] at h
    linarith [h, sq (inner ℝ (b 0) (z p)), sq (inner ℝ (b 1) (z p))]
  -- every ring point is a vertex of the pentagon
  have vertex : ∀ p : Fin 9, 4 ≤ p.val → ∃ m : ℕ, m < 5
      ∧ z p = cos (2 * π * m / 5) • b 0 + sin (2 * π * m / 5) • b 1 := by
    intro p hp
    by_cases h4 : p = 4
    · refine ⟨0, by norm_num, ?_⟩
      rw [h4, ← b0]
      simp
    · have hlt : (4 : Fin 9) < p := by
        rw [Fin.lt_def]
        have : p.val ≠ 4 := fun e => h4 (Fin.ext e)
        show 4 < p.val
        omega
      have hroot := kRR 4 p (by decide) hlt
      rw [← b0] at hroot
      obtain ⟨m, hm1, hm4, ha, hβ⟩ := vertex_of (root_cases hroot) (unit2 p hp)
      refine ⟨m, by omega, ?_⟩
      rw [← ha, ← hβ]
      exact expand p hp
  choose! m hm using vertex
  -- the relabelling
  let σ₀ : Fin 9 → Fin 9 := fun p =>
    if h : 4 ≤ p.val then ⟨m p, lt_trans (hm p h).1 (by norm_num)⟩ else ⟨p.val + 5, by omega⟩
  have hσ4 : ∀ p : Fin 9, (h : 4 ≤ p.val) → (σ₀ p).val = m p := fun p h => by
    simp only [σ₀, dif_pos h]
  have hσ0 : ∀ p : Fin 9, ¬ 4 ≤ p.val → (σ₀ p).val = p.val + 5 := fun p h => by
    simp only [σ₀, dif_neg h]
  have hσinj : Function.Injective σ₀ := by
    intro p q hpq
    have hv := congrArg Fin.val hpq
    by_cases hp : 4 ≤ p.val
    · by_cases hq : 4 ≤ q.val
      · rw [hσ4 p hp, hσ4 q hq] at hv
        apply hzinj
        rw [(hm p hp).2, (hm q hq).2, hv]
      · rw [hσ4 p hp, hσ0 q hq] at hv
        have := (hm p hp).1
        omega
    · by_cases hq : 4 ≤ q.val
      · rw [hσ0 p hp, hσ4 q hq] at hv
        have := (hm q hq).1
        omega
      · rw [hσ0 p hp, hσ0 q hq] at hv
        exact Fin.ext (by omega)
  -- the points of the configuration in the basis
  have key : ∀ p : Fin 9, z p = ∑ j, Cstar (σ₀ p) j • b j := by
    intro p
    rw [Cstar_eq, Fin.sum_univ_four]
    by_cases hp : 4 ≤ p.val
    · rw [hσ4 p hp]
      have h5 := (hm p hp).1
      simp only [CstarN, if_pos h5]
      rw [(hm p hp).2]
      simp
    · rw [hσ0 p hp]
      have hp4 : p.val < 4 := by omega
      obtain ⟨p, hp9⟩ := p
      simp only at hp4 ⊢
      interval_cases p
      · simp [CstarN, b2]
      · simp [CstarN, b2]
        exact e1
      · simp [CstarN, b3]
      · simp [CstarN, b3]
        exact e3
  -- the orthogonal matrix and the permutation
  refine ⟨(EuclideanSpace.basisFun (Fin 4) ℝ).toBasis.toMatrix b,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary (EuclideanSpace.basisFun (Fin 4) ℝ) b,
    μ.symm.trans (Equiv.ofBijective σ₀ (Finite.injective_iff_bijective.1 hσinj)), fun i => ?_⟩
  have hzi : z (μ.symm i) = pt x i := by
    rw [hz]
    simp
  have hk := key (μ.symm i)
  rw [hzi] at hk
  funext c
  have hc := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v c) hk
  simp only [Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, Equiv.trans_apply, Equiv.ofBijective_apply]
  have hpt : (pt x i) c = x i c := rfl
  rw [hpt] at hc
  rw [hc]
  simp [mul_comm]

/-- **The theorem for nine points on the three-sphere**, given the six statements of the certificates. -/
theorem harmonic9_of (h54 : Excl claims54) (hL0 : ExclL0) (hR : Excl claimsRing) (hS : ExclSel claimsSel)
    (hV : ExclLeaves leavesVR) (hI : InnerOK) : Harmonic9 := by
  refine ⟨onSphere_Cstar, injective_Cstar, energy_Cstar, fun x hx hinj => ?_⟩
  obtain ⟨a, b⟩ := lower_and_contacts h54 hL0 hR hS hV hI hx hinj
  refine ⟨a, fun he => ?_⟩
  obtain ⟨μ, _, hK⟩ := b (le_of_eq he)
  exact congruent_of_contacts hx hinj hK

/-- info: 'S3N9.harmonic9_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms harmonic9_of

end S3N9
