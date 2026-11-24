import Mathlib
import Certificates.Theorem.T8A

/-!
# The minimal harmonic energy of 9 points on the sphere S³

The harmonic energy of a configuration of points on the unit sphere `S³` of `ℝ⁴` is the sum of
`1 / r²` over all pairs of points, where `r` is the distance of the two points of a pair. It is
the electrostatic energy of unit charges at these points: in `ℝ⁴` the potential of a point charge
is proportional to `1 / r²`.

This file states which configurations of 9 points on `S³` have the least harmonic energy: the
minimizer consists of a regular pentagon on a great circle and of a square on the orthogonal
great circle, the minimal energy is `35 / 2`, and the minimizer is unique up to orthogonal
transformations and relabelling of the points.

All definitions needed to read the statement are included here.
This companion supplies the complete proof of the statement in `Showcase.lean`.
-/

noncomputable section
open Real

namespace Harmonic9S3

/-! ## Configurations and harmonic energy -/

/-- Four-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 4)

/-- Nine distinct points on the unit sphere `S³` of `ℝ⁴`. -/
def IsConfiguration (Y : Fin 9 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The harmonic energy, summed over the 36 unordered pairs of points: a pair at the distance
`r` contributes `1 / r²`. Here `‖·‖` is the Euclidean norm, and `∑ j with i < j` is the sum over
all `j` with `i < j`.
(For two equal points Lean evaluates `1 / 0` to `0`; the theorem below concerns configurations
of distinct points only.) -/
def E (Y : Fin 9 → Point) : ℝ :=
  ∑ i : Fin 9, ∑ j : Fin 9 with i < j, 1 / ‖Y i - Y j‖ ^ 2

/-- `Y` arises from `Z` by an orthogonal transformation and a permutation of the labels.
Here `Point ≃ₗᵢ[ℝ] Point` is the type of the linear isometries of `ℝ⁴` onto itself, that is, of
the orthogonal transformations (rotations and reflections), and `Equiv.Perm (Fin 9)` is the type
of the permutations of the labels `0, …, 8`. -/
def Congruent (Y Z : Fin 9 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 9)),
    ∀ i, Y i = U (Z (σ i))

/-- `Z` is a configuration that attains the minimum of the energy among all configurations, and
a configuration has the same energy exactly when it is a congruent copy of `Z`. -/
def IsUniqueMinimizer (Z : Fin 9 → Point) : Prop :=
  IsConfiguration Z ∧ ∀ Y, IsConfiguration Y →
    E Z ≤ E Y ∧ (E Y = E Z ↔ Congruent Y Z)

/-! ## The pentagon with the orthogonal square -/

/-- The point `(cos θ, sin θ, 0, 0)` of the unit circle in the plane of the first two coordinates.
Here `!₂[x₁, x₂, x₃, x₄]` is the Euclidean vector with the coordinates `(x₁, x₂, x₃, x₄)`. -/
def circlePoint (θ : ℝ) : Point :=
  !₂[cos θ, sin θ, 0, 0]

/-- `X` consists of the five vertices of a regular pentagon on the unit circle of the plane of the
first two coordinates, at the angles `2 π k / 5` for `k = 0, …, 4`, and of the four points
`(0, 0, ±1, 0)` and `(0, 0, 0, ±1)`: a square on the unit circle of the orthogonal plane.
Here `![x₀, …, x₈]` is the family with the entries `x₀, …, x₈`. -/
def X : Fin 9 → Point :=
  ![circlePoint 0, circlePoint (2 * π / 5), circlePoint (4 * π / 5),
    circlePoint (6 * π / 5), circlePoint (8 * π / 5),
    !₂[0, 0, 1, 0], !₂[0, 0, -1, 0], !₂[0, 0, 0, 1], !₂[0, 0, 0, -1]]

/-! ## Translation to the coordinates of the proof

The proof in `LeanCode` describes a configuration by its coordinates `Fin 9 → Fin 4 → ℝ` and an
orthogonal transformation by its matrix. The lemmas of this section translate its statements to
the definitions above. -/

/-- The coordinates of a configuration. -/
private def coords (Y : Fin 9 → Point) : Fin 9 → Fin 4 → ℝ := fun i => (Y i).ofLp

private theorem pt_coords (Y : Fin 9 → Point) : S3N9.pt (coords Y) = Y := rfl

private theorem isConfiguration_iff (Y : Fin 9 → Point) :
    IsConfiguration Y ↔ S3N9.OnSphere (coords Y) ∧ Function.Injective (coords Y) := by
  rw [S3N9.onSphere_iff, ← S3N9.injective_pt, pt_coords]
  rfl

private theorem E_eq (Y : Fin 9 → Point) : E Y = S3N9.energy (coords Y) := by
  rw [S3N9.energy_eq, pt_coords]
  rfl

/-- The configuration `X` is the configuration of the proof. -/
private theorem coords_X : coords X = S3N9.Cstar := by
  funext n k
  fin_cases n <;> fin_cases k <;>
    simp [coords, X, circlePoint, S3N9.Cstar] <;> ring_nf

/-- An orthogonal matrix preserves the dot product. -/
private theorem dot_mulVec (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v w : Fin 4 → ℝ) :
    ∑ c, U.mulVec v c * U.mulVec w c = ∑ c, v c * w c := by
  have h1 : U.transpose * U = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 4) ℝ).mp hU
  have h2 : dotProduct (U.mulVec v) (U.mulVec w) = dotProduct v w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1,
      Matrix.one_mulVec]
  exact h2

/-- The orthogonal transformation with a given orthogonal matrix. -/
private def isometryOfMatrix (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometry.toLinearIsometryEquiv
    ⟨Matrix.toEuclideanLin U, fun v => by
      have h := dot_mulVec U hU v.ofLp v.ofLp
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simpa [sq] using h⟩ rfl

private theorem isometryOfMatrix_apply (U : Matrix (Fin 4) (Fin 4) ℝ)
    (hU : U ∈ Matrix.orthogonalGroup (Fin 4) ℝ) (v : Point) :
    isometryOfMatrix U hU v = WithLp.toLp 2 (U.mulVec v.ofLp) := rfl

private theorem congruent_of_coords {Y : Fin 9 → Point}
    (h : S3N9.Congruent S3N9.Cstar (coords Y)) : Congruent Y X := by
  obtain ⟨U, hU, σ, hY⟩ := h
  refine ⟨isometryOfMatrix U hU, σ, fun i => ?_⟩
  have hX : (X (σ i)).ofLp = S3N9.Cstar (σ i) := congrFun coords_X (σ i)
  rw [isometryOfMatrix_apply, hX]
  exact congrArg (WithLp.toLp 2) (hY i)

/-- Congruent configurations have the same energy. -/
private theorem E_eq_of_congruent {Y Z : Fin 9 → Point} (h : Congruent Y Z) : E Y = E Z := by
  obtain ⟨U, σ, hY⟩ := h
  have hd : ∀ i j, ‖Y i - Y j‖ = ‖Z (σ i) - Z (σ j)‖ := fun i j => by
    rw [hY i, hY j, ← map_sub, LinearIsometryEquiv.norm_map]
  have h1 : E Y = S3N9.energyE (Z ∘ σ) := by
    simp only [E, S3N9.energyE, hd, Function.comp_apply]
  rw [h1, S3N9.energyE_comp_perm]
  rfl

/-! ## The main theorem -/

/-- **The minimal harmonic energy of 9 points on `S³`.** Here `E` is the harmonic energy, the sum
of `1 / ‖Y i - Y j‖²` over the pairs of points, and `X` is the pentagon with the orthogonal square.

* `X` is a configuration of 9 distinct points on the unit sphere of `ℝ⁴`, every such
  configuration `Y` satisfies `E(X) ≤ E(Y)`, and equality holds exactly when `Y` arises from `X`
  by an orthogonal transformation and a relabelling of the points.
* The minimal energy is `E(X) = 35 / 2`. -/
theorem harmonic_energy_9_points_S3 :
    IsUniqueMinimizer X ∧ E X = 35 / 2 := by
  -- The theorem in the coordinates of the proof (`Certificates/Theorem/T8A.lean`), for the
  -- configuration `S3N9.Cstar` with coordinates `Fin 9 → Fin 4 → ℝ`.
  obtain ⟨hsph, hinj, hE, hmin⟩ : S3N9.Harmonic9 := T8A.harmonic9
  have hEX : E X = 35 / 2 := by rw [E_eq, coords_X]; exact hE
  refine ⟨⟨?_, fun Y hY => ?_⟩, hEX⟩
  · -- the candidate is a configuration
    rw [isConfiguration_iff, coords_X]
    exact ⟨hsph, hinj⟩
  · -- minimality and the case of equality
    obtain ⟨hYs, hYi⟩ := (isConfiguration_iff Y).mp hY
    obtain ⟨hle, heq⟩ := hmin (coords Y) hYs hYi
    rw [hEX, E_eq Y]
    refine ⟨hle, fun h => congruent_of_coords (heq h), fun h => ?_⟩
    rw [← E_eq Y, ← hEX]
    exact E_eq_of_congruent h

/-- info: 'Harmonic9S3.harmonic_energy_9_points_S3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms harmonic_energy_9_points_S3

end Harmonic9S3
