import Mathlib

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

All definitions needed to read the statement are included here, and Mathlib is the only import.
The same statement, with its proof, appears in `Showcase_WithProofs.lean`.
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

/-! ## The main theorem -/

/-- **The minimal harmonic energy of 9 points on `S³`.** Here `E` is the harmonic energy, the sum
of `1 / ‖Y i - Y j‖²` over the pairs of points, and `X` is the pentagon with the orthogonal square.

* `X` is a configuration of 9 distinct points on the unit sphere of `ℝ⁴`, every such
  configuration `Y` satisfies `E(X) ≤ E(Y)`, and equality holds exactly when `Y` arises from `X`
  by an orthogonal transformation and a relabelling of the points.
* The minimal energy is `E(X) = 35 / 2`. -/
theorem harmonic_energy_9_points_S3 :
    IsUniqueMinimizer X ∧ E X = 35 / 2 := by
  sorry

end Harmonic9S3
