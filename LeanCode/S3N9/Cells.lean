module

public import S3N9.Cover

/-!
# The theorem for nine points: the claims of the 54 cells

The source divides the separated configurations into 55 cells by the canonical minima `m₀ ≤ m₁ ≤ m₂ ≤ m₃` (the
inner products of the first four pairs of a chain) and by the number `k` of near pairs, and it assigns one or
several pair claims to every cell other than L3-k2 (`tab:cellclaims`). This file contains these claims as data.
All their bounds are multiples of `1 / 2000`, and a bound is stored as its numerator.

With `θ = -9/10`, `a₁ = -99/100`, `a₀ = -361/400`, `b₀ = -7/8`, `κ₂ = -43/50`, `κ = -4/5`, `ς = -17/20`, the grid
`ξ = (-99/100, -49/50, -97/100, -24/25, -19/20, -47/50, -23/25)` and the slabs `[ξ_j, ξ_{j+1}]`, whose last end is
`a₀` in the first grid and `θ` in the second one, the cells and their claims are the following. `k = j` means
`m_{j-1} ≤ θ < m_j`.

* L0: `m₀ ≥ a₀`. One class of nine points with all inner products at least `a₀` (not a pair claim).
* L1-0j-k1 (`m₀` in the slab `j` of the first grid `[l, h]`, `k = 1`): `P([l,h]; b₀)` if `m₁ ≥ b₀`; otherwise, for
  `j ≤ 4`, `P([l,h],[θ,b₀]; κ₂)` if `m₂ ≥ κ₂` and `P([l,h],[θ,b₀],[θ,κ₂]; θ)` if not, and for `j ≥ 5`
  `P([l,h],[θ,b₀]; θ)` (`lma:coverK1`).
* L1-0j-k2: for `j ≤ 2` the ring cover with `I = [l,h]`, `I' = [l,θ]` and `κ`: `P(I,I'; κ)` if `m₂ ≥ κ`,
  `P(I,I',[θ,κ]; κ)` if `m₂ < κ ≤ m₃`, and `P(I,I',[θ,κ],[θ,κ]; θ)` otherwise, where for `j = 0` the interval `I'` of
  the last claim is cut at `-49/50` and `-19/20` (`lma:coverRING`); for `3 ≤ j ≤ 5` `P([l,h],[l,θ]; κ₂)` if
  `m₂ ≥ κ₂` and `P([l,h],[l,θ],[θ,κ₂]; θ)` if not (`lma:coverK2`); for `j = 6` `P([l,h],[l,θ]; θ)`.
* L1-0j-k3: for `j ≤ 5` the claims `P([l,h],[r_i,r_{i+1}],[r_i,θ]; θ)` with `m₁ ∈ [r_i, r_{i+1}]` for a grid `r`
  from `l` to `θ` (`lma:coverK3`); for `j = 6` `P([l,h],[l,θ],[l,θ]; θ)`.
* L1-0j-k4: `P([l,h],[l,θ],[l,θ],[l,θ]; θ)`.
* L2H: `m₀ ≤ a₁`, `m₁ ≥ b₀`. `P([-1,a₁]; b₀)`.
* L2-0j-k2 (`m₀ ≤ a₁`, `m₁` in the slab `j` of the second grid `[l, h]`): the ring cover with `I = [-1,a₁]`,
  `I' = [l,h]`; for `j = 0` its last claim is replaced by `P(I,I',[θ,ς],[θ,κ]; θ)` if `m₂ ≤ ς` and
  `P(I,I',[ς,κ],[ς,κ]; θ)` if not.
* L2-0j-k3, L2-0j-k4: `P([-1,a₁],[l,h],[l,θ]; θ)` and `P([-1,a₁],[l,h],[l,θ],[l,θ]; θ)`.
* L2U-k1 (`m₀ ≤ a₁`, `θ ≤ m₁ ≤ b₀`, `k = 1`): the ring cover with `I = [-1,a₁]`, `I' = [θ,b₀]`.
* L3-k3, L3-k4 (`m₀, m₁ ≤ a₁`): `P([-1,a₁],[-1,a₁],[-1,θ]; θ)` and the same with one more class `[-1,θ]`.

The list `claims54` has 113 entries, one for every claim of a typed certificate of the 54 cells in the table
`S3N9/claims.tsv` other than the claim of L0.
-/

@[expose] public section

namespace S3N9

/-- The data of a pair claim in units of `1 / 2000`: the intervals of the classes of two points and the lower
bound of the last class. -/
structure PC where
  I : List (ℤ × ℤ)
  l : ℤ
deriving DecidableEq, Repr

/-- A labelled configuration in the pair claim with the data `c`. -/
def InPC (c : PC) (y : Fin 9 → EuclideanSpace ℝ (Fin 4)) : Prop :=
  InPairClaim c.I.length
    (fun i => (((c.I.getD i (0, 0)).1 : ℝ) / 2000, ((c.I.getD i (0, 0)).2 : ℝ) / 2000)) ((c.l : ℝ) / 2000) y

namespace Cell

/-- `θ`, `a₁`, `a₀`, `b₀`, `κ₂`, `κ`, `ς`, `-1`, in units of `1 / 2000`. -/
def th : ℤ := -1800
def a1 : ℤ := -1980
def a0 : ℤ := -1805
def b0 : ℤ := -1750
def k2 : ℤ := -1720
def kr : ℤ := -1600
def sg : ℤ := -1700
def m1 : ℤ := -2000

/-- The grid `ξ₀, …, ξ₆`. -/
def xi : List ℤ := [-1980, -1960, -1940, -1920, -1900, -1880, -1840]

/-- The slab `j` of the first grid (last end `a₀`) and of the second grid (last end `θ`). -/
def g1 (j : ℕ) : ℤ × ℤ := (xi.getD j 0, if j = 6 then a0 else xi.getD (j + 1) 0)
def g2 (j : ℕ) : ℤ × ℤ := (xi.getD j 0, if j = 6 then th else xi.getD (j + 1) 0)

def k1a (s : ℤ × ℤ) : PC := ⟨[s], b0⟩
def k1b (s : ℤ × ℤ) : PC := ⟨[s, (th, b0)], th⟩
def k1b1 (s : ℤ × ℤ) : PC := ⟨[s, (th, b0)], k2⟩
def k1b2 (s : ℤ × ℤ) : PC := ⟨[s, (th, b0), (th, k2)], th⟩
def k2a (s : ℤ × ℤ) : PC := ⟨[s, (s.1, th)], k2⟩
def k2b (s : ℤ × ℤ) : PC := ⟨[s, (s.1, th), (th, k2)], th⟩
def rga (s s' : ℤ × ℤ) : PC := ⟨[s, s'], kr⟩
def rgb (s s' : ℤ × ℤ) : PC := ⟨[s, s', (th, kr)], kr⟩
def rgc (s s' : ℤ × ℤ) : PC := ⟨[s, s', (th, kr), (th, kr)], th⟩
def rgc1 (s s' : ℤ × ℤ) : PC := ⟨[s, s', (th, sg), (th, kr)], th⟩
def rgc2 (s s' : ℤ × ℤ) : PC := ⟨[s, s', (sg, kr), (sg, kr)], th⟩
def k3 (s : ℤ × ℤ) (r r' : ℤ) : PC := ⟨[s, (r, r'), (r, th)], th⟩

/-- The claim of a cell with `n` near pairs that is closed by one claim: `P([l,h],[l,θ],…,[l,θ]; θ)`. -/
def cd (n : ℕ) (s : ℤ × ℤ) : PC := ⟨s :: List.replicate (n - 1) (s.1, th), th⟩

/-- The claims `P(s, [r_i, r_{i+1}], [r_i, θ]; θ)` of a grid `r`. -/
def k3s (s : ℤ × ℤ) : List ℤ → List PC
  | r :: r' :: t => k3 s r r' :: k3s s (r' :: t)
  | _ => []

/-- The grids of the cells L1-0j-k3, `j ≤ 5`. -/
def grid3 (j : ℕ) : List ℤ :=
  if j = 2 then [-1940, -1920, -1880, -1840, th] else xi.drop j ++ [th]

def l2 (s : ℤ × ℤ) : List PC :=
  [⟨[(m1, a1), s, (s.1, th)], th⟩, ⟨[(m1, a1), s, (s.1, th), (s.1, th)], th⟩]

end Cell

open Cell in
/-- **The claims of the 54 cells other than L0 and L3-k2**, in the order of the cells of the source. -/
def claims54 : List PC :=
  -- L1-0j-k1
  ((List.range 5).flatMap fun j => [k1a (g1 j), k1b1 (g1 j), k1b2 (g1 j)])
    ++ [k1a (g1 5), k1b (g1 5), k1a (g1 6), k1b (g1 6)]
    -- L1-0j-k2
    ++ [rga (g1 0) (a1, th), rgb (g1 0) (a1, th), rgc (g1 0) (-1980, -1960), rgc (g1 0) (-1960, -1900),
      rgc (g1 0) (-1900, th)]
    ++ ([1, 2].flatMap fun j => [rga (g1 j) ((g1 j).1, th), rgb (g1 j) ((g1 j).1, th), rgc (g1 j) ((g1 j).1, th)])
    ++ ([3, 4, 5].flatMap fun j => [k2a (g1 j), k2b (g1 j)])
    ++ [cd 2 (g1 6)]
    -- L1-0j-k3
    ++ ((List.range 6).flatMap fun j => k3s (g1 j) (grid3 j))
    ++ [cd 3 (g1 6)]
    -- L1-0j-k4
    ++ ((List.range 7).map fun j => cd 4 (g1 j))
    -- L2H
    ++ [⟨[(m1, a1)], b0⟩]
    -- L2-0j-k2
    ++ [rga (m1, a1) (g2 0), rgb (m1, a1) (g2 0), rgc1 (m1, a1) (g2 0), rgc2 (m1, a1) (g2 0)]
    ++ ((List.range 6).flatMap fun j => [rga (m1, a1) (g2 (j + 1)), rgb (m1, a1) (g2 (j + 1)), rgc (m1, a1) (g2 (j + 1))])
    -- L2-0j-k3 and L2-0j-k4
    ++ ((List.range 7).flatMap fun j => l2 (g2 j))
    -- L2U-k1
    ++ [rga (m1, a1) (th, b0), rgb (m1, a1) (th, b0), rgc (m1, a1) (th, b0)]
    -- L3-k3 and L3-k4
    ++ [⟨[(m1, a1), (m1, a1), (m1, th)], th⟩, ⟨[(m1, a1), (m1, a1), (m1, th), (m1, th)], th⟩]

/-- The list has one entry for every claim of the 54 cells other than the claim of L0. -/
theorem claims54_length : claims54.length = 113 := by decide

end S3N9
