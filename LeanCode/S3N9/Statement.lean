module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The harmonic energy of nine points on the three-sphere: the statement

This file contains the statement of the theorem and nothing else. It uses the real numbers, finite
sums, the cosine and the orthogonal group of Mathlib, and no file of the library `CAP`.

**The configuration.** The configuration `Cstar` consists of the five points
`(cos (2 π k / 5), sin (2 π k / 5), 0, 0)`, `k = 0, …, 4`, a regular pentagon on a great circle, and
of the four points `(0, 0, ±1, 0)` and `(0, 0, 0, ±1)` of the orthogonal plane.

**The theorem** (`Harmonic9`). The nine points of `Cstar` are distinct points of the unit sphere of
`ℝ⁴`, and `energy Cstar = 35 / 2`. Every configuration `x` of nine distinct points of the unit sphere
satisfies `35 / 2 ≤ energy x`, and if equality holds, then `x` arises from `Cstar` by an orthogonal map
and a relabelling of the points. Here `energy x = ∑_{i < j} 1 / |x i - x j|²` is the harmonic energy.

The hypothesis that the points of `x` are distinct is needed in this form: for two equal points
Lean evaluates `1 / 0` to `0`, whereas the energy of such a configuration is infinite.

The file states the theorem as a proposition. Its proof is `T8A.harmonic9` in
`Certificates/Theorem/T8A.lean`, and `Showcase_WithProofs.lean` restates the theorem for points of the
Euclidean space and for linear isometries.
-/

@[expose] public section

namespace S3N9

open Finset

/-- The harmonic energy of `N` points of `ℝ⁴` that are given by their coordinates. -/
noncomputable def energy {N : ℕ} (x : Fin N → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j with i < j, 1 / ∑ k, (x i k - x j k) ^ 2

/-- All points lie on the unit sphere. -/
def OnSphere {N : ℕ} (x : Fin N → Fin 4 → ℝ) : Prop := ∀ i, ∑ k, x i k ^ 2 = 1

/-- The configuration `y` arises from `x` by an orthogonal map and a relabelling of the points. -/
def Congruent {N : ℕ} (x y : Fin N → Fin 4 → ℝ) : Prop :=
  ∃ U ∈ Matrix.orthogonalGroup (Fin 4) ℝ, ∃ σ : Equiv.Perm (Fin N), ∀ i, y i = U.mulVec (x (σ i))

/-- **The regular pentagon with the orthogonal square.** The points `0, …, 4` are the vertices of the
pentagon, the points `5, …, 8` are `e₃`, `-e₃`, `e₄`, `-e₄`. -/
noncomputable def Cstar (n : Fin 9) : Fin 4 → ℝ :=
  if n.val < 5 then ![Real.cos (2 * Real.pi * n.val / 5), Real.sin (2 * Real.pi * n.val / 5), 0, 0]
  else if n.val = 5 then ![0, 0, 1, 0]
  else if n.val = 6 then ![0, 0, -1, 0]
  else if n.val = 7 then ![0, 0, 0, 1]
  else ![0, 0, 0, -1]

/-- **The theorem for nine points on the three-sphere** (`T8`), as a proposition: the regular pentagon
with the orthogonal square is the unique minimizer of the harmonic energy of nine points on the unit
sphere of `ℝ⁴`, up to orthogonal maps and relabelling, and the minimum is `35 / 2`. -/
def Harmonic9 : Prop :=
  OnSphere Cstar ∧ Function.Injective Cstar ∧ energy Cstar = 35 / 2 ∧
    ∀ x : Fin 9 → Fin 4 → ℝ, OnSphere x → Function.Injective x →
      35 / 2 ≤ energy x ∧ (energy x = 35 / 2 → Congruent Cstar x)

/-- The first part of the theorem: the lower bound for the energy. -/
def Minimum9 : Prop :=
  ∀ x : Fin 9 → Fin 4 → ℝ, OnSphere x → Function.Injective x → 35 / 2 ≤ energy x

end S3N9
