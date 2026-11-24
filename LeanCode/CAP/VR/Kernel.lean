module

public import CAP.Wsos.Kernel

/-!
# Virtual-root certificates: the checker (`Init` only)

**State.** The checker is bit-exact with `certgen/vr.py`.

A virtual-root certificate (schema S4) consists of polynomial identities in at most five variables: one
for every record type, one for every label, and one for every minorant. Every identity has the form

  `2 ^ E * Λ - ∑ weights, 2 ^ a * g * ∑ i, ξ i ^ 2 = residual`,

where `Λ` and the weights `g` are polynomials that the data define, the `ξ i` are arbitrary integer
polynomials, and the sum of the absolute values of the coefficients of the residual is at most `rho`.

**One definition, several evaluations.** The polynomials are defined once, for an arbitrary set of
operations `Ops α`: sums, differences and products, multiples, natural numbers, monomials (a monomial
is a natural number whose digits of four bits are the exponents of the five variables), and the sum
of the squares of the columns of a weight. The checker evaluates the definition six times:

* with pairs of natural numbers (`pairOps`): a pair `(p, n)` is the value `p - n` of an integer
  polynomial at the point `X i = 2 ^ (W * k i)`; this is the computation with large numbers;
* with bounds for the sum of the absolute values of the coefficients (`absOps`);
* with bounds for the total degree and for the degree in the pair variables (`degOps`, `pdegOps`);
* with the set of the parity classes of the monomials (`clsOps`);
* with bounds for the slots of the monomials (`posOps`).

**Layouts.** The slot of a monomial is `∑ i, k i * e i`. The strides are injective on the admissible
monomials only: degree at most `D`, pair degree at most `Dp`, parity class zero. The parity class of a
monomial is the sum in `(ℤ/2)²` of the parity vectors of the variables with an odd exponent. A record
polynomial is invariant under sign changes of some variables, so all its monomials have the class
zero, and the columns of a weight are grouped by their class. If the residual is admissible, the
strides are injective on the admissible monomials (a property of the layout, proved once for each
layout), and the coefficients are below `2 ^ W`, then the pair determines the polynomial.

**The residual is computed, and then tested.** From the pair `(p, n)` the checker forms two numbers
`Rp`, `Rn` (`splitRes`; nothing is proved about this step) and tests that `p + Rn = n + Rp`, that the
digits of `Rp`, `Rn` are below `2 ^ wr`, and that the sums of their digits, which are their residues
modulo `2 ^ W - 1`, add up to at most `rho`.

**Columns.** As in `CAP/Wsos`, the polynomials `ξ i` are not data: a block of a weight has a function
`col`, and the checker keeps the bits of `col i` at the places of the monomials of the block (those of
its class, of degree at most `delta` and of pair degree at most `dp`).

**Exact certificates.** A certificate whose bound is attained has residuals zero. Sums of squares of integer
columns do not suffice for it, so a weight may carry an exact part (`ExW`, `Atom`): terms `A(X²) * ζ²`, where the
polynomial `A` has natural coefficients at the squares of the monomials of a mask (the operation `dg`) and `ζ` is a
polynomial given by its monomials and coefficients. The checkers `recordOkX`, `minoOkX` are those of the
identities with these terms; `minoOkX` and the bound `boundOkX` are those of a certificate for the function
`den * f` with a natural number `den`, which stands for a common denominator of the data.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len sqSum)

/-! ## The operations -/

/-- A set of operations on the values of polynomials. -/
structure Ops (α : Type) where
  add : α → α → α
  sub : α → α → α
  mul : α → α → α
  /-- the multiple by a natural number -/
  smul : Nat → α → α
  nat : Nat → α
  /-- the monomial with the exponents `dig c 0, …, dig c 4` -/
  mono : Nat → α
  /-- `sq delta dp cls wb col r`: the sum of the squares of the `r` columns of a block of a weight -/
  sq : Nat → Nat → Nat → Nat → (Nat → Nat) → Nat → α
  /-- `dg delta dp cls wb d`: the polynomial `∑ e, a e * X ^ (2 e)` over the monomials `e` of a mask, where `a e`
  is the digit of width `wb` of `d` at the slot of `X ^ (2 e)` -/
  dg : Nat → Nat → Nat → Nat → Nat → α

/-- A layout: the strides of the five variables (the slot of a monomial is `∑ i, k i * e i`), their
parity vectors (two bits for each variable), the mask of the pair variables, the mask of the variables
that occur in the columns of the weights, and the bounds for the degree and for the pair degree of the
identity. -/
structure Lay where
  k0 : Nat
  k1 : Nat
  k2 : Nat
  k3 : Nat
  k4 : Nat
  pv : Nat
  pm : Nat
  vm : Nat
  D : Nat
  Dp : Nat

/-- The exponent of the variable `i` in a monomial. -/
def dig (c i : Nat) : Nat := Nat.land (Nat.shiftRight c (Nat.mul 4 i)) 15

/-- The bit `i` of a mask. -/
def bitAt (m i : Nat) : Nat := Nat.land (Nat.shiftRight m i) 1

/-- The parity vector of the variable `i`. -/
def pvAt (pv i : Nat) : Nat := Nat.land (Nat.shiftRight pv (Nat.mul 2 i)) 3

/-- The slot of a monomial. -/
def posOf (L : Lay) (c : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul L.k0 (dig c 0)) (Nat.mul L.k1 (dig c 1))) (Nat.mul L.k2 (dig c 2)))
    (Nat.mul L.k3 (dig c 3))) (Nat.mul L.k4 (dig c 4))

/-- The total degree of a monomial. -/
def degOf (c : Nat) : Nat := Nat.add (Nat.add (Nat.add (Nat.add (dig c 0) (dig c 1)) (dig c 2)) (dig c 3)) (dig c 4)

/-- The degree of a monomial in the variables of the mask `pm`. -/
def pdegOf (pm c : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.add (Nat.mul (bitAt pm 0) (dig c 0)) (Nat.mul (bitAt pm 1) (dig c 1)))
    (Nat.mul (bitAt pm 2) (dig c 2))) (Nat.mul (bitAt pm 3) (dig c 3))) (Nat.mul (bitAt pm 4) (dig c 4))

/-- The parity class of a monomial. -/
def clsOf (pv c : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.mul (Nat.land (dig c 0) 1) (pvAt pv 0)) (Nat.mul (Nat.land (dig c 1) 1) (pvAt pv 1)))
    (Nat.mul (Nat.land (dig c 2) 1) (pvAt pv 2))) (Nat.mul (Nat.land (dig c 3) 1) (pvAt pv 3)))
    (Nat.mul (Nat.land (dig c 4) 1) (pvAt pv 4))

def maxN (a b : Nat) : Nat := cond (Nat.ble a b) b a

/-- `k x`, with `x` evaluated first: the kernel then meets the same term for the same value, and finds it
in its table. -/
noncomputable def forceNat {α : Type} (x : Nat) (k : Nat → α) : α := Nat.rec (k 0) (fun n _ => k (Nat.succ n)) x

/-- One variable more: if `H delta p c` is the number of the sum of the monomials of degree at most
`delta`, pair degree at most `p` and class `c` in some variables, then `maskStep s pi f H` is the same
for one variable more, whose value is `2 ^ s`, whose parity vector is `pi` and which counts for the
pair degree if `f = 1`. -/
noncomputable def maskStep (s pi f : Nat) (H : Nat → Nat → Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun p c => H 0 p c)
    (fun delta ih p c => Nat.add (H (Nat.succ delta) p c)
      (cond (Nat.beq f 1 && Nat.beq p 0) 0
        (Nat.shiftLeft (forceNat (Nat.sub p f) (fun p' => forceNat (Nat.xor c pi) (fun c' => ih p' c'))) s)))

def mask0 (_delta _p c : Nat) : Nat := cond (Nat.beq c 0) 1 0

noncomputable def maskVar (W : Nat) (L : Lay) (i k : Nat) (H : Nat → Nat → Nat → Nat) : Nat → Nat → Nat → Nat :=
  cond (Nat.beq (bitAt L.vm i) 1) (maskStep (Nat.mul W k) (pvAt L.pv i) (bitAt L.pm i) H) H

/-- `maskOf W L delta p c`: the number of the polynomial `∑ X ^ e` over the monomials in the variables of
`L.vm` of degree at most `delta`, of pair degree at most `p` and of the class `c`, at the point
`X i = 2 ^ (W * k i)`. -/
noncomputable def maskOf (W : Nat) (L : Lay) : Nat → Nat → Nat → Nat :=
  maskVar W L 4 L.k4 (maskVar W L 3 L.k3 (maskVar W L 2 L.k2 (maskVar W L 1 L.k1 (maskVar W L 0 L.k0 mask0))))

noncomputable def maskAt (W : Nat) (L : Lay) (delta dp c : Nat) : Nat :=
  forceNat delta (fun d => forceNat dp (fun p => forceNat c (fun c' => maskOf W L d p c')))

/-- Pairs of natural numbers: the value of an integer polynomial at the point is `p - n`. -/
noncomputable def pairOps (W : Nat) (L : Lay) : Ops (Nat × Nat) where
  add := fun x y => (Nat.add x.1 y.1, Nat.add x.2 y.2)
  sub := fun x y => (Nat.add x.1 y.2, Nat.add x.2 y.1)
  mul := fun x y => (Nat.add (Nat.mul x.1 y.1) (Nat.mul x.2 y.2), Nat.add (Nat.mul x.1 y.2) (Nat.mul x.2 y.1))
  smul := fun n x => (Nat.mul n x.1, Nat.mul n x.2)
  nat := fun n => (n, 0)
  mono := fun c => (Nat.shiftLeft 1 (Nat.mul W (posOf L c)), 0)
  sq := fun delta dp cls wb col r =>
    ((fun m => sqSum (Nat.mul (mask wb) m) (Nat.shiftLeft m (Nat.pred wb)) col r) (maskAt W L delta dp cls), 0)
  dg := fun delta dp cls wb d => (Nat.land d (Nat.mul (mask wb) (maskAt (Nat.mul 2 W) L delta dp cls)), 0)

/-- Bounds for the sum of the absolute values of the coefficients. -/
noncomputable def absOps (L : Lay) : Ops Nat where
  add := Nat.add
  sub := Nat.add
  mul := Nat.mul
  smul := Nat.mul
  nat := fun n => n
  mono := fun _ => 1
  sq := fun delta dp cls wb _ r =>
    (fun b => Nat.mul r (Nat.mul b b)) (Nat.shiftLeft (maskAt 0 L delta dp cls) (Nat.pred wb))
  dg := fun delta dp cls wb _ => Nat.mul (mask wb) (maskAt 0 L delta dp cls)

/-- Bounds for the total degree. -/
def degOps : Ops Nat where
  add := maxN
  sub := maxN
  mul := Nat.add
  smul := fun _ x => x
  nat := fun _ => 0
  mono := degOf
  sq := fun delta _ _ _ _ _ => Nat.mul 2 delta
  dg := fun delta _ _ _ _ => Nat.mul 2 delta

/-- Bounds for the degree in the variables of the mask `pm`. -/
def pdegOps (pm : Nat) : Ops Nat where
  add := maxN
  sub := maxN
  mul := Nat.add
  smul := fun _ x => x
  nat := fun _ => 0
  mono := pdegOf pm
  sq := fun _ dp _ _ _ _ => Nat.mul 2 dp
  dg := fun _ dp _ _ _ => Nat.mul 2 dp

/-- The largest stride of a layout. -/
def kmax (L : Lay) : Nat := maxN L.k0 (maxN L.k1 (maxN L.k2 (maxN L.k3 L.k4)))

/-- Bounds for the slots of the monomials. -/
def posOps (L : Lay) : Ops Nat where
  add := maxN
  sub := maxN
  mul := Nat.add
  smul := fun _ x => x
  nat := fun _ => 0
  mono := posOf L
  sq := fun delta _ _ _ _ _ => Nat.mul (Nat.mul 2 delta) (kmax L)
  dg := fun delta _ _ _ _ => Nat.mul (Nat.mul 2 delta) (kmax L)

/-- A set of parity classes is a number of four bits. `csetX1 A` consists of the classes `c xor 1`. -/
def csetX1 (A : Nat) : Nat := Nat.lor (Nat.shiftLeft (Nat.land A 5) 1) (Nat.land (Nat.shiftRight A 1) 5)

def csetX2 (A : Nat) : Nat := Nat.lor (Nat.shiftLeft (Nat.land A 3) 2) (Nat.land (Nat.shiftRight A 2) 3)

/-- The sums of a class of `A` and a class of `B`. -/
def csetMul (A B : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (cond (Nat.beq (Nat.land B 1) 1) A 0) (cond (Nat.beq (Nat.land B 2) 2) (csetX1 A) 0))
    (cond (Nat.beq (Nat.land B 4) 4) (csetX2 A) 0)) (cond (Nat.beq (Nat.land B 8) 8) (csetX1 (csetX2 A)) 0)

/-- The set of the parity classes of the monomials. -/
def clsOps (pv : Nat) : Ops Nat where
  add := Nat.lor
  sub := Nat.lor
  mul := fun x y => csetMul (Nat.land x 15) (Nat.land y 15)
  smul := fun n x => cond (Nat.beq n 0) 0 x
  nat := fun n => cond (Nat.beq n 0) 0 1
  mono := fun c => Nat.shiftLeft 1 (clsOf pv c)
  sq := fun _ _ _ _ _ _ => 1
  dg := fun _ _ _ _ _ => 1

/-! ## The data -/

/-- A block of the kernel: the character `((-1) ^ a, (-1) ^ b)`, the flag of the odd blocks, for every
class the exponents `i + 16 * j` of its features and the position of its entries in a column, and the
columns of the factor (digits of width `wb` with the bias `2 ^ (wb - 1)`). -/
structure Blk where
  a : Nat
  b : Nat
  odd : Nat
  wb : Nat
  ex : List (List Nat)
  off : List Nat
  cols : List Nat

/-- The constants of the localizers of a pair class. -/
structure PairConst where
  etan : Nat
  etad : Nat
  aPn : Nat
  aPd : Nat
  aQ2n : Nat
  aQ2d : Nat
  tn : Nat
  td : Nat
  g0 : Nat
  g1 : Nat
  g2 : Nat

/-- The data of a certificate that all identities share. -/
structure Par where
  /-- the degree of the record identities -/
  D : Nat
  mAP : Nat
  mAQ : Nat
  mBP : Nat
  mBQ : Nat
  /-- the width of a coefficient of an exchange polynomial or of a minorant -/
  wP : Nat
  /-- these coefficients and the constants are multiples of `2 ^ -sP` -/
  sP : Nat
  /-- the blocks of `k` are divided by `4 ^ sK k` -/
  sK : List Nat
  kblocks : List (List Blk)
  cA : PairConst
  cB : PairConst
  dirn : Nat
  dird : Nat
  eR2n : Nat
  eR2d : Nat
  /-- the cap of the heights of the ring points: `Gd * h ≤ Gn` -/
  Gn : Nat
  Gd : Nat
  /-- the lower guard of a ring class: `lowD * h ≥ lowN` -/
  lowN : List Nat
  lowD : List Nat
  lamG : Nat
  lamL : List Nat
  /-- the class of a label: `0` for the pair A, `1` for the pair B, `2 + c` for the ring class `c` -/
  dcls : List Nat
  /-- its sign: `1` for the second point of a pair; `0`, `1`, `2` for a ring label in the odd blocks -/
  dsg : List Nat
  /-- the record type of a pair of labels -/
  rt : List Nat

/-- The head of a record type: the data that define its record polynomial. -/
structure RecH where
  /-- `0` AA, `1` BB, `2` AB, `3` A r, `4` B r, `5` a ring type -/
  kind : Nat
  c1 : Nat
  s1 : Nat
  c2 : Nat
  s2 : Nat
  mS : Nat
  mTr : Nat
  jd : Nat
  c0p : Nat
  c0n : Nat
  lop : Nat
  lon : Nat
  lod : Nat
  hip : Nat
  hin : Nat
  hid : Nat
  aS2n : Nat
  aS2d : Nat
  p1ex : List Nat
  p1p : Nat
  p1n : Nat
  p2ex : List Nat
  p2p : Nat
  p2n : Nat
  hform : Nat
  hia : Nat
  hib : Nat
  hex : List Nat
  hp : Nat
  hn : Nat
  hj : Nat
  hc0p : Nat
  hc0n : Nat
  hm : Nat
  cp : Nat
  cn : Nat

/-- The squares of one parity class of a weight: `∑ i < r, ξ i ^ 2`; `ξ i` has the monomials of the class
`cls`, of degree at most `delta` and of pair degree at most `dp`, with the coefficients
`(digit of width wb of col i at the slot of the monomial) - 2 ^ (wb - 1)`. -/
structure WBlk where
  cls : Nat
  delta : Nat
  dp : Nat
  wb : Nat
  r : Nat
  col : Nat → Nat

/-- The squares of a weight: `2 ^ a * g * ∑ blocks, ∑ i, ξ i ^ 2`. -/
structure Weight where
  a : Nat
  blocks : List WBlk

/-- The sum-of-squares side of a record type and the parameters of its evaluation. -/
structure RecX where
  L : Lay
  W : Nat
  E : Nat
  aH : Nat
  aC : Nat
  aP : Nat
  aK : List Nat
  ws : List Weight
  lex : List Nat
  lp : Nat
  ln : Nat
  aL : Nat
  wr : Nat
  rho : Nat

/-- The identity of a minorant. -/
structure MinoX where
  L : Lay
  W : Nat
  E : Nat
  aH : Nat
  ws : List Weight
  wr : Nat
  rho : Nat

/-- The identity of a label. -/
structure ClsX where
  label : Nat
  L : Lay
  W : Nat
  E : Nat
  aP : Nat
  aK : List Nat
  aL : Nat
  wr : Nat
  rho : Nat

/-! ## Lists -/

section Generic

variable {α : Type}

noncomputable def nthL : List (List Nat) → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun h _ ih i => Nat.rec (motive := fun _ => List Nat) h (fun j _ => ih j) i)

noncomputable def isNil : List Nat → Bool := List.rec true (fun _ _ _ => false)

noncomputable def lenB : List (List Blk) → Nat := List.rec 0 (fun _ _ ih => Nat.succ ih)

noncomputable def hdA (o : Ops α) : List α → α := List.rec (o.nat 0) (fun h _ _ => h)

noncomputable def tlA : List α → List α := List.rec [] (fun _ t _ => t)

/-- The exponents `i + 16 * j` of a point, at the variables `ip` and `iq`. -/
def codeAt (ip iq c : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (Nat.land c 15) (Nat.mul 4 ip)) (Nat.shiftLeft (Nat.shiftRight c 4) (Nat.mul 4 iq))

/-- The variable `i`. -/
def var (o : Ops α) (i : Nat) : α := o.mono (Nat.shiftLeft 1 (Nat.mul 4 i))

def sqr (o : Ops α) (x : α) : α := o.mul x x

noncomputable def monoListAt (o : Ops α) (ip iq : Nat) : List Nat → List α :=
  List.rec [] (fun c _ ih => o.mono (codeAt ip iq c) :: ih)

noncomputable def lsumG (o : Ops α) : List α → α := List.rec (o.nat 0) (fun m _ ih => o.add m ih)

/-- `U + ∑ j, (digit j of N) * ms j` -/
noncomputable def dot (o : Ops α) (w mw : Nat) : List α → Nat → α → α :=
  List.rec (motive := fun _ => Nat → α → α) (fun _ U => U)
    (fun m _ ih N U => ih (Nat.shiftRight N w) (o.add U (o.smul (Nat.land N mw) m)))

/-- The polynomial with the coefficients `(digit j of Np) - (digit j of Nn)` at the monomials `cf c`;
a coefficient changes its sign where `fl c` holds. -/
noncomputable def dotGo (o : Ops α) (w mw : Nat) (cf : Nat → Nat) (fl : Nat → Bool) :
    List Nat → Nat → Nat → α → α → α :=
  List.rec (motive := fun _ => Nat → Nat → α → α → α) (fun _ _ P N => o.sub P N)
    (fun c _ ih Np Nn P N =>
      cond (fl c)
        (ih (Nat.shiftRight Np w) (Nat.shiftRight Nn w) (o.add P (o.smul (Nat.land Nn mw) (o.mono (cf c))))
          (o.add N (o.smul (Nat.land Np mw) (o.mono (cf c)))))
        (ih (Nat.shiftRight Np w) (Nat.shiftRight Nn w) (o.add P (o.smul (Nat.land Np mw) (o.mono (cf c))))
          (o.add N (o.smul (Nat.land Nn mw) (o.mono (cf c))))))

/-- The sign of the monomial `i + 16 * j` when the first variable is replaced by its negative
(`tp = 1`) and the second one (`tq = 1`). -/
def flipBit (tp tq c : Nat) : Nat := Nat.land (Nat.xor (Nat.land tp c) (Nat.land tq (Nat.shiftRight c 4))) 1

/-- A polynomial in the two coordinates of a point, at the variables `ip`, `iq`. -/
noncomputable def dotS (o : Ops α) (w tp tq ip iq : Nat) (codes : List Nat) (Np Nn : Nat) : α :=
  dotGo o w (mask w) (codeAt ip iq) (fun c => Nat.beq (flipBit tp tq c) 1) codes Np Nn (o.nat 0) (o.nat 0)

/-- A polynomial in the five variables. -/
noncomputable def dot5 (o : Ops α) (w : Nat) (codes : List Nat) (Np Nn : Nat) : α :=
  dotGo o w (mask w) (fun c => c) (fun _ => false) codes Np Nn (o.nat 0) (o.nat 0)

/-! ## The classes

The coordinates of a point of a class with the shift `m` are `u = U / 2 ^ m`, `v = V / 2 ^ m`. A point of
the pair A with the class coordinates `(p, q)` has `u = ± (1 - p / 2 ^ mAP)`, `v = q / 2 ^ mAQ`; a point
of the pair B has `v = ± (1 - p / 2 ^ mBP)`, `u = q / 2 ^ mBQ`; a ring point has `(u, v) = (p, q)`. -/

def clsM (P : Par) (cls : Nat) : Nat :=
  cond (Nat.beq cls 0) (maxN P.mAP P.mAQ) (cond (Nat.beq cls 1) (maxN P.mBP P.mBQ) 0)

/-- `2 ^ m * (1 - p / 2 ^ mP)` for a pair class -/
def clsMaj (o : Ops α) (P : Par) (cls ip : Nat) : α :=
  o.sub (o.nat (Nat.shiftLeft 1 (clsM P cls)))
    (o.smul (Nat.shiftLeft 1 (Nat.sub (clsM P cls) (cond (Nat.beq cls 0) P.mAP P.mBP))) (var o ip))

/-- `2 ^ m * q / 2 ^ mQ` for a pair class -/
def clsMin (o : Ops α) (P : Par) (cls iq : Nat) : α :=
  o.smul (Nat.shiftLeft 1 (Nat.sub (clsM P cls) (cond (Nat.beq cls 0) P.mAQ P.mBQ))) (var o iq)

def signed (o : Ops α) (sg : Nat) (x : α) : α := cond (Nat.beq sg 1) (o.sub (o.nat 0) x) x

def clsU (o : Ops α) (P : Par) (cls sg ip iq : Nat) : α :=
  cond (Nat.beq cls 0) (signed o sg (clsMaj o P cls ip)) (cond (Nat.beq cls 1) (clsMin o P cls iq) (var o ip))

def clsV (o : Ops α) (P : Par) (cls sg ip iq : Nat) : α :=
  cond (Nat.beq cls 0) (clsMin o P cls iq) (cond (Nat.beq cls 1) (signed o sg (clsMaj o P cls ip)) (var o iq))

/-- `4 ^ m - U ^ 2 - V ^ 2` -/
def clsR (o : Ops α) (m : Nat) (U V : α) : α :=
  o.sub (o.nat (Nat.shiftLeft 1 (Nat.mul 2 m))) (o.add (sqr o U) (sqr o V))

/-! ## The geometry of a record type -/

/-- The inner product of the two end points is `T / 2 ^ mT`. -/
def recMT (P : Par) (h : RecH) : Nat :=
  cond (Nat.beq h.kind 0) (Nat.mul 2 (clsM P h.c1))
    (cond (Nat.beq h.kind 1) (Nat.succ (Nat.mul 2 (clsM P h.c1)))
      (cond (Nat.beq h.kind 2) (Nat.add (Nat.add h.mS (clsM P h.c1)) (clsM P h.c2))
        (cond (Nat.ble h.kind 4) h.mS h.mTr)))

def recT (o : Ops α) (P : Par) (h : RecH) (U1 V1 U2 V2 : α) : α :=
  cond (Nat.beq h.kind 0) (o.sub (o.nat (Nat.shiftLeft 1 (Nat.mul 2 (clsM P h.c1)))) (o.smul 2 (sqr o U1)))
    (cond (Nat.beq h.kind 1)
      (o.sub (o.nat (Nat.shiftLeft 2 (Nat.mul 2 (clsM P h.c1)))) (o.add (sqr o (o.sub U1 U2)) (sqr o (o.sub V1 V2))))
      (cond (Nat.beq h.kind 2)
        (o.add (o.smul (Nat.shiftLeft 1 (Nat.add (clsM P h.c1) (clsM P h.c2))) (var o 4))
          (o.add (o.smul (Nat.shiftLeft 1 (Nat.add h.mS (clsM P h.c2))) V1)
            (o.smul (Nat.shiftLeft 1 (Nat.add h.mS (clsM P h.c1))) U2)))
        (cond (Nat.beq h.kind 3) (o.add (var o 4) (o.smul (Nat.shiftLeft 1 h.mS) U2))
          (cond (Nat.beq h.kind 4) (o.add (var o 4) (o.smul (Nat.shiftLeft 1 h.mS) V2))
            (o.sub (o.add (o.nat h.c0p) (o.smul (Nat.shiftLeft 1 h.jd) (var o 4))) (o.nat h.c0n))))))

/-- `2 ^ (m1 + m2) * T - 2 ^ mT * (U1 * U2 + V1 * V2)` -/
def recHv (o : Ops α) (m1 m2 mT : Nat) (U1 V1 U2 V2 T : α) : α :=
  o.sub (o.smul (Nat.shiftLeft 1 (Nat.add m1 m2)) T) (o.smul (Nat.shiftLeft 1 mT) (o.add (o.mul U1 U2) (o.mul V1 V2)))

noncomputable def qGo (o : Ops α) (H Wt : α) (mT : Nat) : Nat → Nat → α → α → List α :=
  Nat.rec (motive := fun _ => Nat → α → α → List α) (fun _ _ _ => [])
    (fun _ ih k prev cur => cur :: ih (Nat.succ k) cur
      (cond (Nat.beq k 0) H
        (o.sub (o.smul 2 (o.mul H cur)) (o.smul (Nat.shiftLeft 1 (Nat.mul 2 mT)) (o.mul Wt prev)))))

/-- `[Q 0, …, Q (n - 1)]` with `Q k = 2 * H * Q (k - 1) - 4 ^ mT * Wt * Q (k - 2)` -/
noncomputable def qList (o : Ops α) (H Wt : α) (mT n : Nat) : List α := qGo o H Wt mT n 0 (o.nat 0) (o.nat 1)

/-! ## The kernel -/

/-- The sign of the features of a point in a block: `0` for zero, `1` for plus, `2` for minus. -/
def sgnOf (cls sg : Nat) (blk : Blk) : Nat :=
  cond (Nat.beq cls 0) (cond (Nat.beq sg 1 && Nat.beq blk.a 1) 2 1)
    (cond (Nat.beq cls 1) (cond (Nat.beq sg 1 && Nat.beq blk.b 1) 2 1)
      (cond (Nat.beq blk.odd 1) (cond (Nat.beq sg 0) 0 (cond (Nat.beq sg 1) 1 2)) 1))

def sgnMul (s t : Nat) : Nat := cond (Nat.beq s 0 || Nat.beq t 0) 0 (cond (Nat.beq s t) 1 2)

/-- `(∑ columns, D1 * D2, ∑ columns, D1, ∑ columns, D2)` for the polynomials `D1`, `D2` of a column at the
two end points, with the digits of the column as coefficients. -/
noncomputable def colsGo (o : Ops α) (wb mw : Nat) (ms1 ms2 : List α) (o1 o2 : Nat) : List Nat → α × α × α :=
  List.rec (o.nat 0, o.nat 0, o.nat 0)
    (fun col _ ih =>
      (fun D1 D2 => (o.add ih.1 (o.mul D1 D2), o.add ih.2.1 D1, o.add ih.2.2 D2))
        (dot o wb mw ms1 (Nat.shiftRight col o1) (o.nat 0)) (dot o wb mw ms2 (Nat.shiftRight col o2) (o.nat 0)))

/-- `∑ columns, ψ1 * ψ2` for the polynomials `ψ = ∑ f, (digit f - β) * (monomial f)` of a column for the
classes of the two end points, in their variables. -/
noncomputable def blkBil (o : Ops α) (blk : Blk) (c1 i1p i1q c2 i2p i2q : Nat) : α :=
  cond (isNil (nthL blk.ex c1) || isNil (nthL blk.ex c2)) (o.nat 0)
    ((fun ms1 ms2 =>
      (fun S1 S2 t beta =>
        o.sub (o.add t.1 (o.smul (Nat.mul (len blk.cols) (Nat.mul beta beta)) (o.mul S1 S2)))
          (o.smul beta (o.add (o.mul t.2.1 S2) (o.mul S1 t.2.2))))
        (lsumG o ms1) (lsumG o ms2)
        (colsGo o blk.wb (mask blk.wb) ms1 ms2 (Nat.mul blk.wb (nth blk.off c1)) (Nat.mul blk.wb (nth blk.off c2)) blk.cols)
        (Nat.shiftLeft 1 (Nat.pred blk.wb)))
      (monoListAt o i1p i1q (nthL blk.ex c1)) (monoListAt o i2p i2q (nthL blk.ex c2)))

/-- `acc + ∑ blocks, ± ∑ columns, ψ1 * ψ2` for the blocks of one `k`. -/
noncomputable def innerK (o : Ops α) (c1 s1 i1p i1q c2 s2 i2p i2q : Nat) : List Blk → α → α :=
  List.rec (motive := fun _ => α → α) (fun acc => acc)
    (fun blk _ ih acc =>
      ih (cond (Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 0) acc
        (cond (Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 1)
          (o.add acc (blkBil o blk c1 i1p i1q c2 i2p i2q))
          (o.sub acc (blkBil o blk c1 i1p i1q c2 i2p i2q)))))

/-- A block of this list has features of both classes. -/
noncomputable def usedK (c1 c2 : Nat) : List Blk → Bool :=
  List.rec false (fun blk _ ih => (!(isNil (nthL blk.ex c1)) && !(isNil (nthL blk.ex c2))) || ih)

/-- `acc + ∑ k, 2 ^ aK k * Q k * inner k` -/
noncomputable def kernGo (o : Ops α) (c1 s1 i1p i1q c2 s2 i2p i2q : Nat) :
    List (List Blk) → List α → List Nat → α → α :=
  List.rec (motive := fun _ => List α → List Nat → α → α) (fun _ _ acc => acc)
    (fun blks _ ih qs aK acc =>
      ih (tlA qs) (tl aK)
        (cond (usedK c1 c2 blks)
          (o.add acc (o.smul (Nat.shiftLeft 1 (hd aK))
            (o.mul (hdA o qs) (innerK o c1 s1 i1p i1q c2 s2 i2p i2q blks (o.nat 0)))))
          acc))

/-! ## The minorant inside a record -/

/-- `∑ r, c r * 2 ^ (mH * (n - r)) * that ^ r` for the `n + 1` coefficients `c r = (digit r of hp) - (digit r of hn)` -/
noncomputable def hornerGo (o : Ops α) (w mw hp hn : Nat) (that : α) (mH : Nat) : Nat → Nat → α → α :=
  Nat.rec (motive := fun _ => Nat → α → α) (fun _ acc => acc)
    (fun r ih i acc => ih (Nat.succ i)
      (o.add (o.mul acc that)
        (o.smul (Nat.shiftLeft 1 (Nat.mul mH i))
          (o.sub (o.nat (Nat.land (Nat.shiftRight hp (Nat.mul w r)) mw))
            (o.nat (Nat.land (Nat.shiftRight hn (Nat.mul w r)) mw))))))

/-- `2 ^ (hm + mT)` times the centred inner product `2 ^ hj * (t - c0)` -/
def recThat (o : Ops α) (h : RecH) (T : α) (mT : Nat) : α :=
  o.smul (Nat.shiftLeft 1 h.hj)
    (o.sub (o.add (o.smul (Nat.shiftLeft 1 h.hm) T) (o.nat (Nat.shiftLeft h.hc0n mT))) (o.nat (Nat.shiftLeft h.hc0p mT)))

noncomputable def recHm (o : Ops α) (P : Par) (h : RecH) (T : α) (mT : Nat) : α :=
  cond (Nat.beq h.hform 0) (dotS o P.wP 0 0 h.hia h.hib h.hex h.hp h.hn)
    (hornerGo o P.wP (mask P.wP) h.hp h.hn (recThat o h T mT) (Nat.add h.hm mT) (len h.hex) 0 (o.nat 0))

/-! ## The localizers -/

/-- The six localizers of an end point of a pair class. -/
noncomputable def locPair (o : Ops α) (P : Par) (cls ip iq : Nat) (R : α) (m : Nat) : List α :=
  (fun c maj mn2 E =>
    [R,
     o.sub (o.nat (Nat.mul c.etan E)) (o.smul c.etad R),
     o.sub (o.nat c.aPn) (o.smul c.aPd (var o ip)),
     o.sub (o.nat c.aQ2n) (o.smul c.aQ2d (sqr o (var o iq))),
     o.sub (o.smul c.tn (sqr o maj)) (o.smul c.td mn2),
     o.sub (o.nat (Nat.mul c.g0 E)) (o.add (o.smul c.g1 R) (o.smul c.g2 mn2))])
    (cond (Nat.beq cls 0) P.cA P.cB) (clsMaj o P cls ip) (sqr o (clsMin o P cls iq)) (Nat.shiftLeft 1 (Nat.mul 2 m))

/-- The five localizers of a ring end point. -/
noncomputable def locRing (o : Ops α) (P : Par) (cls ip iq : Nat) (R : α) : List α :=
  (fun p2 q2 =>
    [R,
     o.sub (o.nat P.eR2n) (o.smul P.eR2d p2),
     o.sub (o.nat P.eR2n) (o.smul P.eR2d q2),
     o.sub (o.nat P.Gn) (o.smul P.Gd (o.add p2 q2)),
     o.sub (o.smul (nth P.lowD (Nat.sub cls 2)) (o.add p2 q2)) (o.nat (nth P.lowN (Nat.sub cls 2)))])
    (sqr o (var o ip)) (sqr o (var o iq))

noncomputable def locEnd (o : Ops α) (P : Par) (cls ip iq : Nat) (R : α) (m : Nat) : List α :=
  cond (Nat.blt cls 2) (locPair o P cls ip iq R m) (locRing o P cls ip iq R)

/-- `lod * hid * 4 ^ mT * (t - lo) * (hi - t)` -/
def locT (o : Ops α) (h : RecH) (T : α) (mT : Nat) : α :=
  o.mul
    (o.sub (o.add (o.smul h.lod T) (o.nat (Nat.mul h.lon (Nat.shiftLeft 1 mT)))) (o.nat (Nat.mul h.lop (Nat.shiftLeft 1 mT))))
    (o.sub (o.nat (Nat.mul h.hip (Nat.shiftLeft 1 mT))) (o.add (o.smul h.hid T) (o.nat (Nat.mul h.hin (Nat.shiftLeft 1 mT)))))

/-- `4 ^ (m1 + m2 + mT) * (1 - a1 ^ 2 - a2 ^ 2 - t ^ 2 + 2 * a1 * a2 * t)` -/
def locG3 (o : Ops α) (A1 A2 T : α) (m1 m2 mT : Nat) : α :=
  o.sub
    (o.add (o.nat (Nat.shiftLeft 1 (Nat.mul 2 (Nat.add (Nat.add m1 m2) mT))))
      (o.smul (Nat.shiftLeft 1 (Nat.succ (Nat.add (Nat.add m1 m2) mT))) (o.mul (o.mul A1 A2) T)))
    (o.add (o.add (o.smul (Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m2 mT))) (sqr o A1))
        (o.smul (Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m1 mT))) (sqr o A2)))
      (o.smul (Nat.shiftLeft 1 (Nat.mul 2 (Nat.add m1 m2))) (sqr o T)))

/-- The weights of a record type, in the order of its kind; the first one is `1`. -/
noncomputable def recLocs (o : Ops α) (P : Par) (h : RecH) (i2p i2q m1 m2 mT : Nat)
    (U1 V1 U2 V2 T R1 R2 H Wt : α) : List α :=
  o.nat 1 :: (locEnd o P h.c1 0 1 R1 m1 ++
    (cond (Nat.beq h.kind 0) [] (locEnd o P h.c2 i2p i2q R2 m2) ++
      (locT o h T mT ::
        (cond (Nat.ble 2 h.kind && Nat.ble h.kind 4)
            [o.sub (o.nat h.aS2n) (o.smul h.aS2d (sqr o (var o 4)))] [] ++
          (locG3 o U1 U2 T m1 m2 mT :: locG3 o V1 V2 T m1 m2 mT ::
            (cond (Nat.ble 2 h.kind) [o.sub (o.smul (Nat.shiftLeft 1 (Nat.mul 2 mT)) Wt) (sqr o H)] [] ++
              cond (Nat.beq h.kind 1)
                [o.sub (o.smul P.dirn (sqr o (o.sub V1 V2))) (o.smul P.dird (sqr o (o.sub U1 U2)))] []))))))

/-- `∑ blocks, ∑ i, ξ i ^ 2` -/
noncomputable def sqBlocks (o : Ops α) : List WBlk → α :=
  List.rec (o.nat 0) (fun b _ ih => o.add (o.sq b.delta b.dp b.cls b.wb b.col b.r) ih)

/-- `acc + ∑ w, 2 ^ a w * g w * ∑ blocks, ∑ i, ξ i ^ 2`; the weights are in the order of the localizers. -/
noncomputable def sosGo (o : Ops α) : List Weight → List α → α → α :=
  List.rec (motive := fun _ => List α → α → α) (fun _ acc => acc)
    (fun w _ ih locs acc => ih (tlA locs)
      (o.add acc (o.smul (Nat.shiftLeft 1 w.a) (o.mul (hdA o locs) (sqBlocks o w.blocks)))))

/-! ## The value of a record -/

/-- `2 ^ E * (h - C - 2 * K - π₁ - π₂)` -/
noncomputable def recLhs (o : Ops α) (P : Par) (h : RecH) (x : RecX) (i2p i2q mT : Nat) (T H Wt : α) : α :=
  o.sub (o.add (o.smul (Nat.shiftLeft 1 x.aH) (recHm o P h T mT)) (o.nat (Nat.shiftLeft h.cn x.aC)))
    (o.add
      (o.add (o.nat (Nat.shiftLeft h.cp x.aC))
        (kernGo o h.c1 h.s1 0 1 h.c2 h.s2 i2p i2q P.kblocks (qList o H Wt mT (lenB P.kblocks)) x.aK (o.nat 0)))
      (o.smul (Nat.shiftLeft 1 x.aP)
        (o.add (dotS o P.wP 0 0 0 1 h.p1ex h.p1p h.p1n) (dotS o P.wP 0 0 i2p i2q h.p2ex h.p2p h.p2n))))

noncomputable def recValK (o : Ops α) (P : Par) (h : RecH) (x : RecX) (i2p i2q m1 m2 mT : Nat)
    (U1 V1 U2 V2 T R1 R2 : α) : α :=
  (fun H Wt =>
    o.sub (recLhs o P h x i2p i2q mT T H Wt)
      (cond (Nat.beq h.kind 1)
        (o.add (sosGo o x.ws (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2 H Wt) (o.nat 0))
          (o.smul (Nat.shiftLeft 1 x.aL) (o.mul (o.sub R2 R1) (dot5 o P.wP x.lex x.lp x.ln))))
        (sosGo o x.ws (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2 H Wt) (o.nat 0))))
    (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)

noncomputable def recValU (o : Ops α) (P : Par) (h : RecH) (x : RecX) (i2p i2q m1 m2 : Nat) (U1 V1 U2 V2 : α) : α :=
  recValK o P h x i2p i2q m1 m2 (recMT P h) U1 V1 U2 V2 (recT o P h U1 V1 U2 V2) (clsR o m1 U1 V1) (clsR o m2 U2 V2)

/-- The residual of the identity of a record type: `2 ^ E * L - S`. -/
noncomputable def recVal (o : Ops α) (P : Par) (h : RecH) (x : RecX) : α :=
  (fun i2p i2q =>
    recValU o P h x i2p i2q (clsM P h.c1) (clsM P h.c2) (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1)
      (clsU o P h.c2 h.s2 i2p i2q) (clsV o P h.c2 h.s2 i2p i2q))
    (cond (Nat.beq h.kind 0) 0 2) (cond (Nat.beq h.kind 0) 1 3)

/-! ## The identity of a minorant -/

def minoBiv (h : RecH) : Bool := Nat.beq h.kind 3 || Nat.beq h.kind 4

def minoMM (h : RecH) : Nat :=
  cond (minoBiv h) h.mS (cond (Nat.beq h.hform 1) (Nat.add h.hm h.hj) h.mTr)

/-- `2 ^ mM` times the inner product, in the variables of the minorant. -/
def minoT (o : Ops α) (h : RecH) : α :=
  cond (minoBiv h) (o.add (o.smul (Nat.shiftLeft 1 h.mS) (var o 0)) (var o 1))
    (cond (Nat.beq h.hform 1)
      (o.sub (o.add (o.nat (Nat.shiftLeft h.hc0p h.hj)) (o.smul (Nat.shiftLeft 1 h.hm) (var o 0))) (o.nat (Nat.shiftLeft h.hc0n h.hj)))
      (o.sub (o.add (o.nat h.c0p) (o.smul (Nat.shiftLeft 1 h.jd) (var o 0))) (o.nat h.c0n)))

noncomputable def minoLocs (o : Ops α) (P : Par) (h : RecH) (T : α) (mM : Nat) : List α :=
  cond (minoBiv h)
    [o.nat 1,
     o.sub (o.nat P.eR2n) (o.smul P.eR2d (sqr o (var o 0))),
     o.sub (o.nat h.aS2n) (o.smul h.aS2d (sqr o (var o 1))),
     locT o h T mM]
    [o.sub (o.add (o.smul h.lod T) (o.nat (Nat.mul h.lon (Nat.shiftLeft 1 mM)))) (o.nat (Nat.mul h.lop (Nat.shiftLeft 1 mM))),
     o.sub (o.nat (Nat.mul h.hip (Nat.shiftLeft 1 mM))) (o.add (o.smul h.hid T) (o.nat (Nat.mul h.hin (Nat.shiftLeft 1 mM))))]

/-- The residual of the identity of a minorant: `2 ^ E * (1 - 2 * (1 - t) * h) - S`. -/
noncomputable def minoVal (o : Ops α) (P : Par) (h : RecH) (x : MinoX) : α :=
  (fun mM T =>
    o.sub
      (o.sub (o.nat (Nat.shiftLeft 1 x.E))
        (o.smul (Nat.shiftLeft 1 x.aH) (o.mul (o.sub (o.nat (Nat.shiftLeft 1 mM)) T) (dotS o P.wP 0 0 0 1 h.hex h.hp h.hn))))
      (sosGo o x.ws (minoLocs o P h T mM) (o.nat 0)))
    (minoMM h) (minoT o h)

/-! ## The identity of a label -/

noncomputable def nthH : List RecH → Nat → RecH :=
  List.rec (motive := fun _ => Nat → RecH)
    (fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, [], 0, 0, [], 0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => RecH) h (fun j _ => ih j) i)

/-- The position of the pair `i < j` of labels in the list of the 36 pairs. -/
def pairIndex (i j : Nat) : Nat := Nat.add (Nat.div (Nat.mul j (Nat.pred j)) 2) i

/-- The record type of the pair of the labels `l ≠ o`. -/
noncomputable def headOf (P : Par) (heads : List RecH) (l o : Nat) : RecH :=
  nthH heads (nth P.rt (cond (Nat.blt l o) (pairIndex l o) (pairIndex o l)))

/-- The first coordinate of the label `l` changes its sign in the data of its pair with the label `o`. -/
def flipP (l o : Nat) : Nat := cond (Nat.ble 4 l && Nat.beq o 1) 1 0

def flipQ (l o : Nat) : Nat :=
  cond ((Nat.ble l 1 && Nat.beq o 3) || (Nat.ble 2 l && Nat.ble l 3 && Nat.beq o 1) || (Nat.ble 4 l && Nat.beq o 3)) 1 0

/-- The exchange polynomial of the label `l` towards the label `o`, in the class coordinates of `l`. -/
noncomputable def piTerm (o : Ops α) (P : Par) (heads : List RecH) (l ot : Nat) : α :=
  cond (Nat.blt l ot)
    (dotS o P.wP (flipP l ot) (flipQ l ot) 0 1 (headOf P heads l ot).p1ex (headOf P heads l ot).p1p (headOf P heads l ot).p1n)
    (dotS o P.wP (flipP l ot) (flipQ l ot) 0 1 (headOf P heads l ot).p2ex (headOf P heads l ot).p2p (headOf P heads l ot).p2n)

/-- `acc + ∑ o < n, o ≠ l, π (l; o)` -/
noncomputable def clsPhiGo (o : Ops α) (P : Par) (heads : List RecH) (l : Nat) : Nat → α → α :=
  Nat.rec (motive := fun _ => α → α) (fun acc => acc)
    (fun ot ih acc => ih (cond (Nat.beq ot l) acc (o.add acc (piTerm o P heads l ot))))

/-- `acc + ∑ k, 2 ^ aK k * R ^ k * inner k` at two coinciding points -/
noncomputable def clsDeltaGo (o : Ops α) (cls sg : Nat) (R : α) : List (List Blk) → List Nat → α → α → α :=
  List.rec (motive := fun _ => List Nat → α → α → α) (fun _ _ acc => acc)
    (fun blks _ ih aK Rk acc =>
      ih (tl aK) (o.mul Rk R)
        (cond (usedK cls cls blks)
          (o.add acc (o.smul (Nat.shiftLeft 1 (hd aK)) (o.mul Rk (innerK o cls sg 0 1 cls sg 0 1 blks (o.nat 0)))))
          acc))

/-- The guard term of a label, in the unit `2 ^ -sP`: `lamG * h ^ 2 * (Gn - Gd * h) + lamL * lowD * h`. -/
noncomputable def clsLam (o : Ops α) (P : Par) (cls : Nat) : α :=
  cond (Nat.blt cls 2) (o.nat 0)
    ((fun hgt =>
      o.add (o.smul P.lamG (o.mul (sqr o hgt) (o.sub (o.nat P.Gn) (o.smul P.Gd hgt))))
        (o.smul (Nat.mul (nth P.lamL (Nat.sub cls 2)) (nth P.lowD (Nat.sub cls 2))) hgt))
      (o.add (sqr o (var o 0)) (sqr o (var o 1))))

/-- The residual of the identity of a label: `2 ^ E * (∑ π - K - Λ)`. -/
noncomputable def clsVal (o : Ops α) (P : Par) (heads : List RecH) (x : ClsX) : α :=
  (fun cls sg =>
    o.sub (o.smul (Nat.shiftLeft 1 x.aP) (clsPhiGo o P heads x.label 9 (o.nat 0)))
      (o.add
        (clsDeltaGo o cls sg (clsR o (clsM P cls) (clsU o P cls sg 0 1) (clsV o P cls sg 0 1)) P.kblocks x.aK (o.nat 1) (o.nat 0))
        (o.smul (Nat.shiftLeft 1 x.aL) (clsLam o P cls))))
    (nth P.dcls x.label) (nth P.dsg x.label)

end Generic

/-! ## The test of a residual -/

/-- Numbers `(Rp, Rn)` with `P + Rn = N + Rp` and small digits, if the digits of `P - N` in the base `2 ^ W`
are small. Nothing is proved about this function: the checker tests its values. -/
def splitRes (W slots P N : Nat) : Nat × Nat :=
  (fun half => (fun Y => (fun top => (fun full =>
      (Nat.sub (Nat.land Y full) top, Nat.sub (Nat.sub half top) (Nat.sub Y (Nat.land Y full))))
    (Nat.mul (Nat.shiftRight top (Nat.pred W)) (mask W))) (Nat.land Y half)) (Nat.sub (Nat.add P half) N))
    (Nat.shiftLeft (ones W slots) (Nat.pred W))

/-- `P - N = Rp - Rn` for two numbers with `slots` digits below `2 ^ wr`, whose sums of digits add up to at
most `rho`. -/
def resTest (W slots wr rho P N Rp Rn : Nat) : Bool :=
  Nat.beq (Nat.add P Rn) (Nat.add N Rp) && Nat.ble 1 W && Nat.ble wr W
    && Nat.beq (Nat.shiftRight Rp (Nat.mul W slots)) 0 && Nat.beq (Nat.shiftRight Rn (Nat.mul W slots)) 0
    && Nat.beq (Nat.land Rp (Nat.mul (ones W slots) (Nat.sub (Nat.shiftLeft 1 W) (Nat.shiftLeft 1 wr)))) 0
    && Nat.beq (Nat.land Rn (Nat.mul (ones W slots) (Nat.sub (Nat.shiftLeft 1 W) (Nat.shiftLeft 1 wr)))) 0
    && Nat.blt (Nat.shiftLeft slots wr) (mask W)
    && Nat.ble (Nat.add (Nat.mod Rp (mask W)) (Nat.mod Rn (mask W))) rho

def residualOk (W slots wr rho P N : Nat) : Bool :=
  resTest W slots wr rho P N (splitRes W slots P N).1 (splitRes W slots P N).2

/-- The columns of a block are polynomials with small coefficients whose squares are admissible. -/
noncomputable def blocksOk (W : Nat) (L : Lay) : List WBlk → Bool :=
  List.rec true (fun b _ ih =>
    Nat.ble 1 b.wb && Nat.ble b.wb W && Nat.ble (Nat.mul 2 b.delta) L.D && Nat.ble (Nat.mul 2 b.dp) L.Dp && Nat.ble b.cls 3
      && Nat.ble (Nat.shiftLeft (maskAt 0 L b.delta b.dp b.cls) b.wb) (Nat.shiftLeft 1 W) && ih)

noncomputable def weightsOk (W : Nat) (L : Lay) : List Weight → Bool :=
  List.rec true (fun w _ ih => blocksOk W L w.blocks && ih)

/-- The tests that all identities share: the columns of the weights; the degree, the pair degree and the
parity class of the residual; the bound for its coefficients; and the residual itself. -/
noncomputable def runOk (L : Lay) (W wr rho : Nat) (ws : List Weight) (val : Nat × Nat) (bound deg pdeg pos cs : Nat) : Bool :=
  weightsOk W L ws && Nat.ble deg L.D && Nat.ble pdeg L.Dp && Nat.beq (Nat.land cs 14) 0
    && Nat.ble (Nat.add bound (Nat.shiftLeft 1 wr)) (Nat.shiftLeft 1 W) && residualOk W (Nat.succ pos) wr rho val.1 val.2

/-! ## The layouts -/

/-- The strides of a layout are injective on the admissible monomials (degree at most `D`, pair degree at most
`Dp`, class zero, in all five variables): there are fewer than `2 ^ w` of them, and the number of their sum at
the slot width `w` has `slots` digits, each of them `0` or `1`. -/
noncomputable def layoutOk (L : Lay) (w slots : Nat) : Bool :=
  (fun L' =>
    (fun M =>
      Nat.ble 1 w && Nat.blt (maskAt 0 L' L.D L.Dp 0) (Nat.shiftLeft 1 w)
        && Nat.beq (Nat.shiftRight M (Nat.mul w slots)) 0
        && Nat.beq (Nat.land M (Nat.mul (ones w slots) (Nat.sub (Nat.shiftLeft 1 w) 2))) 0)
      (maskAt w L' L.D L.Dp 0))
    (Lay.mk L.k0 L.k1 L.k2 L.k3 L.k4 L.pv L.pm 31 L.D L.Dp)

/-! ## The checkers -/

noncomputable def kScalesGo (c1 c2 eH E1 : Nat) : List (List Blk) → List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) (fun _ _ _ => true)
    (fun blks _ ih aK sK k =>
      (!(usedK c1 c2 blks) || Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul eH k)) (Nat.mul 2 (hd sK))) E1)
        && ih (tl aK) (tl sK) (Nat.succ k))

/-- The exponents of the terms of a record identity fit its scale `2 ^ E`. -/
noncomputable def recScalesOk (P : Par) (h : RecH) (x : RecX) : Bool :=
  Nat.beq (Nat.add x.aC P.sP) x.E && Nat.beq (Nat.add x.aP P.sP) x.E
    && cond (Nat.beq h.hform 0) (Nat.beq (Nat.add x.aH P.sP) x.E)
        (Nat.ble 1 (len h.hex)
          && Nat.beq (Nat.add (Nat.add x.aH P.sP) (Nat.mul (Nat.add h.hm (recMT P h)) (Nat.pred (len h.hex)))) x.E)
    && kScalesGo h.c1 h.c2 (Nat.add (Nat.add (recMT P h) (clsM P h.c1)) (clsM P h.c2)) (Nat.succ x.E) P.kblocks x.aK P.sK 0

/-- The checker of a record type. -/
noncomputable def recordOk (P : Par) (h : RecH) (x : RecX) : Bool :=
  recScalesOk P h x
    && runOk x.L x.W x.wr x.rho x.ws (recVal (pairOps x.W x.L) P h x) (recVal (absOps x.L) P h x) (recVal degOps P h x)
        (recVal (pdegOps x.L.pm) P h x) (recVal (posOps x.L) P h x) (recVal (clsOps x.L.pv) P h x)

/-- The checker of a minorant. -/
noncomputable def minoOk (P : Par) (h : RecH) (x : MinoX) : Bool :=
  Nat.beq (Nat.add (Nat.add x.aH (minoMM h)) P.sP) (Nat.succ x.E)
    && runOk x.L x.W x.wr x.rho x.ws (minoVal (pairOps x.W x.L) P h x) (minoVal (absOps x.L) P h x) (minoVal degOps P h x)
        (minoVal (pdegOps x.L.pm) P h x) (minoVal (posOps x.L) P h x) (minoVal (clsOps x.L.pv) P h x)

noncomputable def cScalesGo (cls m E : Nat) : List (List Blk) → List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool) (fun _ _ _ => true)
    (fun blks _ ih aK sK k =>
      (!(usedK cls cls blks) || Nat.beq (Nat.add (Nat.add (hd aK) (Nat.mul (Nat.mul 2 m) k)) (Nat.mul 2 (hd sK))) E)
        && ih (tl aK) (tl sK) (Nat.succ k))

/-- The checker of the identity of a label. -/
noncomputable def clsOk (P : Par) (heads : List RecH) (x : ClsX) : Bool :=
  Nat.beq (Nat.add x.aP P.sP) x.E && Nat.beq (Nat.add x.aL P.sP) x.E && Nat.blt x.label 9
    && cScalesGo (nth P.dcls x.label) (clsM P (nth P.dcls x.label)) x.E P.kblocks x.aK P.sK 0
    && runOk x.L x.W x.wr x.rho [] (clsVal (pairOps x.W x.L) P heads x) (clsVal (absOps x.L) P heads x)
        (clsVal degOps P heads x) (clsVal (pdegOps x.L.pm) P heads x) (clsVal (posOps x.L) P heads x)
        (clsVal (clsOps x.L.pv) P heads x)

/-! ## The labels and the record types -/

noncomputable def allN (f : Nat → Bool) : Nat → Bool := Nat.rec true (fun k ih => ih && f k)

noncomputable def allH (f : RecH → Bool) : List RecH → Bool := List.rec true (fun h _ ih => f h && ih)

def sgFlip (s : Nat) : Nat := cond (Nat.beq s 1) 2 (cond (Nat.beq s 2) 1 0)

/-- The exponents `i + 16 * j` of a polynomial in two variables are below `16`. -/
noncomputable def codesOk : List Nat → Bool := List.rec true (fun c _ ih => Nat.blt c 256 && ih)

/-- The exponents are `k, k + 1, …` in this order, and below `16`. -/
noncomputable def iotaOk : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih k => Nat.beq c k && Nat.blt c 16 && ih (Nat.succ k))

/-- The exponents of the exchange polynomials, and the form of the minorant: a polynomial in the variables
`(2, 4)` of a record of the kind A r, `(3, 4)` of the kind B r and `(4, 0)` of a ring type, or a polynomial in
the centred inner product for the kinds other than A r and B r. -/
noncomputable def formOk (h : RecH) : Bool :=
  codesOk h.p1ex && codesOk h.p2ex
    && cond (Nat.beq h.hform 0)
        (codesOk h.hex
          && ((Nat.beq h.kind 3 && Nat.beq h.hia 2 && Nat.beq h.hib 4)
            || (Nat.beq h.kind 4 && Nat.beq h.hia 3 && Nat.beq h.hib 4)
            || (Nat.beq h.kind 5 && Nat.beq h.hia 4 && Nat.beq h.hib 0)))
        (Nat.beq h.hform 1 && iotaOk h.hex 0 && !(Nat.beq h.kind 3) && !(Nat.beq h.kind 4))

/-- The classes of the end points of a record type fit its kind, and its polynomials have the form of its
kind. -/
noncomputable def headOk (h : RecH) : Bool :=
  formOk h
    && cond (Nat.beq h.kind 0) (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.beq h.c2 0 && Nat.beq h.s2 1)
      (cond (Nat.beq h.kind 1) (Nat.beq h.c1 1 && Nat.beq h.s1 0 && Nat.beq h.c2 1 && Nat.beq h.s2 1)
        (cond (Nat.beq h.kind 2) (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.beq h.c2 1 && Nat.beq h.s2 0)
          (cond (Nat.beq h.kind 3) (Nat.beq h.c1 0 && Nat.beq h.s1 0 && Nat.ble 2 h.c2)
            (cond (Nat.beq h.kind 4) (Nat.beq h.c1 1 && Nat.beq h.s1 0 && Nat.ble 2 h.c2)
              (Nat.beq h.kind 5 && Nat.ble 2 h.c1 && Nat.ble 2 h.c2 && Nat.ble h.s1 2 && Nat.ble h.s2 2)))))

noncomputable def lenH : List RecH → Nat := List.rec 0 (fun _ _ ih => Nat.succ ih)

/-- The record type of the pair `i < j` of labels has the classes of the two labels. -/
noncomputable def pairOk (P : Par) (heads : List RecH) (i j : Nat) : Bool :=
  Nat.blt (nth P.rt (pairIndex i j)) (lenH heads) && (fun h =>
    cond (Nat.ble j 1) (Nat.beq h.kind 0)
      (cond (Nat.ble 2 i && Nat.ble j 3) (Nat.beq h.kind 1)
        (cond (Nat.ble i 1 && Nat.ble j 3) (Nat.beq h.kind 2)
          (cond (Nat.ble i 1) (Nat.beq h.kind 3 && Nat.beq h.c2 (nth P.dcls j))
            (cond (Nat.ble i 3) (Nat.beq h.kind 4 && Nat.beq h.c2 (nth P.dcls j))
              (Nat.beq h.kind 5 && Nat.beq h.c1 (nth P.dcls i) && Nat.beq h.c2 (nth P.dcls j)
                && ((Nat.beq (nth P.dsg i) h.s1 && Nat.beq (nth P.dsg j) h.s2)
                  || (Nat.beq (nth P.dsg i) (sgFlip h.s1) && Nat.beq (nth P.dsg j) (sgFlip h.s2)))))))))
    (nthH heads (nth P.rt (pairIndex i j)))

/-- The parities of the features of one class in a block with the character `(a, b)`; the exponents are
below `16`. -/
noncomputable def exOk (cls a b odd : Nat) : List Nat → Bool :=
  List.rec true (fun c _ ih =>
    Nat.blt c 256
      && cond (Nat.beq cls 0) (Nat.beq (Nat.land (Nat.shiftRight c 4) 1) b && Nat.beq odd 0)
        (cond (Nat.beq cls 1) (Nat.beq (Nat.land (Nat.shiftRight c 4) 1) a && Nat.beq odd 0)
          (Nat.beq (Nat.land c 1) a && Nat.beq (Nat.land (Nat.shiftRight c 4) 1) b)) && ih)

noncomputable def exAll (a b odd : Nat) : List (List Nat) → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun ex _ ih cls => exOk cls a b odd ex && ih (Nat.succ cls))

noncomputable def blkParOk : List Blk → Bool := List.rec true (fun blk _ ih => exAll blk.a blk.b blk.odd blk.ex 0 && ih)

/-- The parities of the features: in a block with the character `(a, b)` the features of the pair A have the
parity `b` in `q`, those of the pair B the parity `a` in `q`, and those of a ring class the parities `a` in
`p` and `b` in `q`; an odd block has features of ring classes only. -/
noncomputable def kblocksOk : List (List Blk) → Bool := List.rec true (fun blks _ ih => blkParOk blks && ih)

/-- The interval `[lo, hi]` of a record type lies in `[(c0 - 2 ^ jd) / 2 ^ mT, (c0 + 2 ^ jd) / 2 ^ mT]`. -/
def intervalOk (c0p c0n jd mT : Nat) (h : RecH) : Bool :=
  Nat.ble (Nat.add (Nat.mul h.lod c0p) (Nat.mul h.lon (Nat.shiftLeft 1 mT)))
      (Nat.add (Nat.mul h.lod (Nat.add c0n (Nat.shiftLeft 1 jd))) (Nat.mul h.lop (Nat.shiftLeft 1 mT)))
    && Nat.ble (Nat.add (Nat.mul h.hip (Nat.shiftLeft 1 mT)) (Nat.mul h.hid c0n))
      (Nat.add (Nat.mul h.hid (Nat.add c0p (Nat.shiftLeft 1 jd))) (Nat.mul h.hin (Nat.shiftLeft 1 mT)))

/-- The last variable of a record type and the variable of its minorant lie in `[-1, 1]` on the interval of
the inner product; the interval ends below `1`, and its ends are ordered. -/
def rangesOk (h : RecH) : Bool :=
  Nat.blt h.hip (Nat.add h.hid h.hin) && Nat.ble 1 h.lod && Nat.ble 1 h.hid
    && Nat.ble (Nat.add (Nat.mul h.lop h.hid) (Nat.mul h.hin h.lod)) (Nat.add (Nat.mul h.hip h.lod) (Nat.mul h.lon h.hid))
    && (!(Nat.beq h.kind 5) || intervalOk h.c0p h.c0n h.jd h.mTr h)
    && (!(Nat.ble 2 h.kind && Nat.ble h.kind 4) || (Nat.ble h.aS2n h.aS2d && Nat.ble 1 h.aS2d))
    && (!(Nat.beq h.hform 1) || intervalOk (Nat.shiftLeft h.hc0p h.hj) (Nat.shiftLeft h.hc0n h.hj) h.hm (Nat.add h.hm h.hj) h)

def pcOk (c : PairConst) : Bool :=
  Nat.ble c.aPn c.aPd && Nat.ble c.aQ2n c.aQ2d && Nat.ble 1 c.aPd && Nat.ble 1 c.aQ2d && Nat.ble 1 c.etad && Nat.ble 1 c.td
    && Nat.ble 1 c.g2

/-- The class coordinates lie in `[-1, 1]`. -/
def constsOk (P : Par) : Bool :=
  pcOk P.cA && pcOk P.cB && Nat.ble P.eR2n P.eR2d && Nat.ble 1 P.eR2d && Nat.ble 1 P.dird

/-- The labels `0, 1` are the points of the pair A, the labels `2, 3` those of the pair B, the labels
`4, …, 8` are ring points; every pair of labels has a record type of its kind with its classes. -/
noncomputable def labelsOk (P : Par) (heads : List RecH) : Bool :=
  Nat.beq (nth P.dcls 0) 0 && Nat.beq (nth P.dcls 1) 0 && Nat.beq (nth P.dcls 2) 1 && Nat.beq (nth P.dcls 3) 1
    && Nat.beq (nth P.dsg 0) 0 && Nat.beq (nth P.dsg 1) 1 && Nat.beq (nth P.dsg 2) 0 && Nat.beq (nth P.dsg 3) 1
    && Nat.beq (len P.dcls) 9 && Nat.beq (len P.dsg) 9
    && allN (fun l => Nat.ble l 3 || Nat.ble 2 (nth P.dcls l)) 9
    && allH headOk heads && allH rangesOk heads && constsOk P
    && allN (fun j => allN (fun i => pairOk P heads i j) j) 9 && kblocksOk P.kblocks

/-! ## The bound -/

/-- The scale and the norm of the residual of an identity. -/
structure Loss where
  E : Nat
  rho : Nat

noncomputable def nthLoss : List Loss → Nat → Loss :=
  List.rec (motive := fun _ => Nat → Loss) (fun _ => ⟨0, 0⟩)
    (fun h _ ih i => Nat.rec (motive := fun _ => Loss) h (fun j _ => ih j) i)

/-- For every record type: `F` is at least its scale, and `gm / 2 ^ F` is at least the loss of its minorant,
`rho * hid / (2 ^ (E + 1) * (hid - hi))`. -/
noncomputable def gmOk (P : Par) (F : Nat) : List RecH → List Loss → List Loss → List Nat → Bool :=
  List.rec (motive := fun _ => List Loss → List Loss → List Nat → Bool) (fun _ _ _ => true)
    (fun h _ ih rl ml gm =>
      Nat.ble (nthLoss rl 0).E F && Nat.ble P.sP F && Nat.blt h.hip (Nat.add h.hid h.hin)
        && Nat.ble (Nat.shiftLeft (Nat.mul (nthLoss ml 0).rho h.hid) F)
            (Nat.shiftLeft (Nat.mul (hd gm) (Nat.sub (Nat.add h.hid h.hin) h.hip)) (Nat.succ (nthLoss ml 0).E))
        && ih (tlL rl) (tlL ml) (tl gm))
where
  tlL : List Loss → List Loss := List.rec [] (fun _ t _ => t)

noncomputable def sumN (f : Nat → Nat) : Nat → Nat := Nat.rec 0 (fun k ih => Nat.add ih (f k))

/-- The bound of the certificate exceeds `Bn / Bd`: with the constants `cp - cn` of the record types of the
36 pairs of labels, the norms of the residuals of the records, the losses of the minorants, the norms of the
residuals of the nine labels, and the terms of the lower guards. -/
noncomputable def boundOk (P : Par) (heads : List RecH) (rl ml cl : List Loss) (gm : List Nat) (F Bn Bd : Nat) : Bool :=
  gmOk P F heads rl ml gm && allN (fun l => Nat.ble (nthLoss cl l).E F) 9
    && Nat.blt
      (Nat.add (Nat.shiftLeft Bn F)
        (Nat.mul Bd (Nat.add
          (sumN (fun j => sumN (fun i =>
            (fun xi => Nat.add (Nat.add (Nat.shiftLeft (nthH heads xi).cn (Nat.sub F P.sP))
                (Nat.shiftLeft (nthLoss rl xi).rho (Nat.sub F (nthLoss rl xi).E))) (nth gm xi))
              (nth P.rt (pairIndex i j))) j) 9)
          (sumN (fun l => Nat.shiftLeft (nthLoss cl l).rho (Nat.sub F (nthLoss cl l).E)) 9))))
      (Nat.mul Bd (Nat.add
        (sumN (fun j => sumN (fun i => Nat.shiftLeft (nthH heads (nth P.rt (pairIndex i j))).cp (Nat.sub F P.sP)) j) 9)
        (sumN (fun l => cond (Nat.ble 2 (nth P.dcls l))
          (Nat.shiftLeft (Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2))) (Nat.sub F P.sP)) 0) 9)))

/-! ## Exact parts of the weights

An exact certificate has `rho = 0` in all identities. Besides the squares of its columns a weight then carries
terms `A(X²) * ζ²` with natural coefficients of `A`: such a term is nonnegative at every real point. -/

/-- A term of the exact part of a weight: `(∑ e, a e * X ^ (2 e)) * ζ ^ 2`. The monomials `e` are those of the class
`cls`, of degree at most `delta` and of pair degree at most `dp`; `a e` is the digit of width `wb` of `d` at the slot
of `X ^ (2 e)`; the polynomial `ζ` has the coefficients `(digit of zp) - (digit of zn)` of width `wz` at the
monomials `zc`. -/
structure Atom where
  cls : Nat
  delta : Nat
  dp : Nat
  wb : Nat
  d : Nat
  wz : Nat
  zc : List Nat
  zp : Nat
  zn : Nat

/-- The exact part of a weight: `2 ^ b * g * ∑ atoms`. -/
structure ExW where
  b : Nat
  ats : List Atom

section Exact

variable {α : Type}

noncomputable def atomVal (o : Ops α) (t : Atom) : α :=
  o.mul (o.dg t.delta t.dp t.cls t.wb t.d) (sqr o (dot5 o t.wz t.zc t.zp t.zn))

/-- `∑ atoms, A(X²) * ζ²` -/
noncomputable def sqAtoms (o : Ops α) : List Atom → α := List.rec (o.nat 0) (fun t _ ih => o.add (atomVal o t) ih)

noncomputable def hdX : List ExW → ExW := List.rec ⟨0, []⟩ (fun h _ _ => h)

noncomputable def tlX : List ExW → List ExW := List.rec [] (fun _ t _ => t)

/-- `acc + ∑ w, g w * (2 ^ a w * ∑ blocks, ∑ i, ξ i ^ 2 + 2 ^ b w * ∑ atoms)`; the weights and their exact parts are
in the order of the localizers. -/
noncomputable def sosGoX (o : Ops α) : List Weight → List ExW → List α → α → α :=
  List.rec (motive := fun _ => List ExW → List α → α → α) (fun _ _ acc => acc)
    (fun w _ ih ex locs acc => ih (tlX ex) (tlA locs)
      (o.add acc (o.mul (hdA o locs)
        (o.add (o.smul (Nat.shiftLeft 1 w.a) (sqBlocks o w.blocks))
          (o.smul (Nat.shiftLeft 1 (hdX ex).b) (sqAtoms o (hdX ex).ats))))))

noncomputable def recValKX (o : Ops α) (P : Par) (h : RecH) (x : RecX) (ex : List ExW) (i2p i2q m1 m2 mT : Nat)
    (U1 V1 U2 V2 T R1 R2 : α) : α :=
  (fun H Wt =>
    o.sub (recLhs o P h x i2p i2q mT T H Wt)
      (cond (Nat.beq h.kind 1)
        (o.add (sosGoX o x.ws ex (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2 H Wt) (o.nat 0))
          (o.smul (Nat.shiftLeft 1 x.aL) (o.mul (o.sub R2 R1) (dot5 o P.wP x.lex x.lp x.ln))))
        (sosGoX o x.ws ex (recLocs o P h i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2 H Wt) (o.nat 0))))
    (recHv o m1 m2 mT U1 V1 U2 V2 T) (o.mul R1 R2)

noncomputable def recValUX (o : Ops α) (P : Par) (h : RecH) (x : RecX) (ex : List ExW) (i2p i2q m1 m2 : Nat)
    (U1 V1 U2 V2 : α) : α :=
  recValKX o P h x ex i2p i2q m1 m2 (recMT P h) U1 V1 U2 V2 (recT o P h U1 V1 U2 V2) (clsR o m1 U1 V1) (clsR o m2 U2 V2)

/-- The residual of the identity of a record type with exact parts: `2 ^ E * L - S`. -/
noncomputable def recValX (o : Ops α) (P : Par) (h : RecH) (x : RecX) (ex : List ExW) : α :=
  (fun i2p i2q =>
    recValUX o P h x ex i2p i2q (clsM P h.c1) (clsM P h.c2) (clsU o P h.c1 h.s1 0 1) (clsV o P h.c1 h.s1 0 1)
      (clsU o P h.c2 h.s2 i2p i2q) (clsV o P h.c2 h.s2 i2p i2q))
    (cond (Nat.beq h.kind 0) 0 2) (cond (Nat.beq h.kind 0) 1 3)

/-- The residual of the identity of a minorant of the function `den * f`, with exact parts:
`2 ^ E * (den - 2 * (1 - t) * h) - S`. -/
noncomputable def minoValX (o : Ops α) (P : Par) (h : RecH) (x : MinoX) (ex : List ExW) (den : Nat) : α :=
  (fun mM T =>
    o.sub
      (o.sub (o.nat (Nat.shiftLeft den x.E))
        (o.smul (Nat.shiftLeft 1 x.aH) (o.mul (o.sub (o.nat (Nat.shiftLeft 1 mM)) T) (dotS o P.wP 0 0 0 1 h.hex h.hp h.hn))))
      (sosGoX o x.ws ex (minoLocs o P h T mM) (o.nat 0)))
    (minoMM h) (minoT o h)

end Exact

/-- The masks of the atoms fit the layout, as those of the blocks. -/
noncomputable def atomsOk (W : Nat) (L : Lay) : List Atom → Bool :=
  List.rec true (fun t _ ih =>
    Nat.ble 1 t.wb && Nat.ble t.wb W && Nat.ble (Nat.mul 2 t.delta) L.D && Nat.ble (Nat.mul 2 t.dp) L.Dp && Nat.ble t.cls 3
      && Nat.ble (Nat.shiftLeft (maskAt 0 L t.delta t.dp t.cls) t.wb) (Nat.shiftLeft 1 W) && ih)

noncomputable def exwOk (W : Nat) (L : Lay) : List ExW → Bool := List.rec true (fun w _ ih => atomsOk W L w.ats && ih)

/-- The checker of a record type with exact parts. -/
noncomputable def recordOkX (P : Par) (h : RecH) (x : RecX) (ex : List ExW) : Bool :=
  recScalesOk P h x && exwOk x.W x.L ex
    && runOk x.L x.W x.wr x.rho x.ws (recValX (pairOps x.W x.L) P h x ex) (recValX (absOps x.L) P h x ex)
        (recValX degOps P h x ex) (recValX (pdegOps x.L.pm) P h x ex) (recValX (posOps x.L) P h x ex)
        (recValX (clsOps x.L.pv) P h x ex)

/-- The checker of a minorant of the function `den * f`, with exact parts. -/
noncomputable def minoOkX (P : Par) (h : RecH) (x : MinoX) (ex : List ExW) (den : Nat) : Bool :=
  Nat.beq (Nat.add (Nat.add x.aH (minoMM h)) P.sP) (Nat.succ x.E) && exwOk x.W x.L ex
    && runOk x.L x.W x.wr x.rho x.ws (minoValX (pairOps x.W x.L) P h x ex den) (minoValX (absOps x.L) P h x ex den)
        (minoValX degOps P h x ex den) (minoValX (pdegOps x.L.pm) P h x ex den) (minoValX (posOps x.L) P h x ex den)
        (minoValX (clsOps x.L.pv) P h x ex den)

/-- The bound of an exact certificate for the function `den * f` is at least `Bn / Bd`: the sum of the constants
`cp - cn` of the record types of the 36 pairs of labels and of the terms of the lower guards, in the unit
`2 ^ -sP`, divided by `den`. -/
noncomputable def boundOkX (P : Par) (heads : List RecH) (den Bn Bd : Nat) : Bool :=
  Nat.ble 1 den && Nat.ble 1 Bd
    && Nat.ble
      (Nat.add (Nat.shiftLeft (Nat.mul Bn den) P.sP)
        (Nat.mul Bd (sumN (fun j => sumN (fun i => (nthH heads (nth P.rt (pairIndex i j))).cn) j) 9)))
      (Nat.mul Bd (Nat.add
        (sumN (fun j => sumN (fun i => (nthH heads (nth P.rt (pairIndex i j))).cp) j) 9)
        (sumN (fun l => cond (Nat.ble 2 (nth P.dcls l))
          (Nat.mul (nth P.lamL (Nat.sub (nth P.dcls l) 2)) (nth P.lowN (Nat.sub (nth P.dcls l) 2))) 0) 9)))

/-! ## The contacts of an exact certificate

If the bound of an exact certificate is attained at a configuration of its piece, then the minorant of every pair
touches the function there, and every term of the minorant identity vanishes. A term `a * ζ ^ 2` of the exact part
of a weight `g`, with a number `a ≥ 1`, then gives `g * ζ ^ 2 = 0`. The checker `contactOk` finds the terms that
give the contact of a record type. -/

noncomputable def lenW : List Weight → Nat := List.rec 0 (fun _ _ ih => Nat.succ ih)

/-- The list is `[c]`. -/
noncomputable def isOne (c : Nat) : List Nat → Bool := List.rec false (fun a t _ => Nat.beq a c && isNil t)

/-- The list is `[c0, c1]`. -/
noncomputable def isTwo (c0 c1 : Nat) : List Nat → Bool := List.rec false (fun a t _ => Nat.beq a c0 && isOne c1 t)

/-- The term is `a * ζ ^ 2` with a number `a ≥ 1`: its polynomial `A` is the constant `a`, the digit of `d` at the
slot zero. -/
def atomConst (W : Nat) (t : Atom) : Bool :=
  Nat.beq t.cls 0 && Nat.beq t.delta 0 && Nat.ble 1 (Nat.land (Nat.land t.d (mask (Nat.mul 2 W))) (mask t.wb))

/-- The term is `a * (X ^ c) ^ 2` with a number `a ≥ 1`. -/
noncomputable def atomMono (W c : Nat) (t : Atom) : Bool :=
  atomConst W t && Nat.beq t.wz 1 && isOne c t.zc && Nat.beq t.zp 1 && Nat.beq t.zn 0

/-- The term is `a * (qa * X₀ ^ 2 - qb) ^ 2` with a number `a ≥ 1`. -/
noncomputable def atomQuad (W qa qb : Nat) (t : Atom) : Bool :=
  atomConst W t && isTwo 0 2 t.zc && Nat.beq (Nat.land t.zp (mask t.wz)) 0
    && Nat.beq (Nat.land (Nat.shiftRight t.zp t.wz) (mask t.wz)) qa
    && Nat.beq (Nat.land t.zn (mask t.wz)) qb && Nat.beq (Nat.land (Nat.shiftRight t.zn t.wz) (mask t.wz)) 0

noncomputable def anyAtom (p : Atom → Bool) : List Atom → Bool := List.rec false (fun t _ ih => p t || ih)

/-- The interval of a record type has an interior: `lo < hi`. -/
def ivOk (h : RecH) : Bool :=
  Nat.blt (Nat.add (Nat.mul h.lop h.hid) (Nat.mul h.hin h.lod)) (Nat.add (Nat.mul h.hip h.lod) (Nat.mul h.lon h.hid))

/-- The terms of the exact parts of the minorant of a record type that give its contact.

* AA, BB: the weight `t - lo` has the term `a * 1 ^ 2`, so the inner product is the lower end of its interval;
* A r, B r: the weight `1` has the terms `a * X₁ ^ 2` and `a * (X₀ ^ 2) ^ 2`, so both variables of the minorant vanish;
* AB: both weights have the term `a * X₀ ^ 2`, so the variable of the minorant vanishes;
* a ring type: both weights have the term `a * (qa * X₀ ^ 2 - qb) ^ 2`, so `qa * m ^ 2 = qb` for the variable `m` of
  the minorant. -/
noncomputable def contactOk (h : RecH) (x : MinoX) (ex : List ExW) (qa qb : Nat) : Bool :=
  cond (Nat.ble h.kind 1)
    (Nat.ble 1 (lenW x.ws) && anyAtom (atomMono x.W 0) (hdX ex).ats)
    (cond (minoBiv h)
      (Nat.ble 1 (lenW x.ws) && anyAtom (atomMono x.W 16) (hdX ex).ats && anyAtom (atomMono x.W 2) (hdX ex).ats)
      (cond (Nat.beq h.kind 2)
        (Nat.ble 2 (lenW x.ws) && ivOk h && anyAtom (atomMono x.W 1) (hdX ex).ats
          && anyAtom (atomMono x.W 1) (hdX (tlX ex)).ats)
        (Nat.ble 2 (lenW x.ws) && ivOk h && anyAtom (atomQuad x.W qa qb) (hdX ex).ats
          && anyAtom (atomQuad x.W qa qb) (hdX (tlX ex)).ats)))

end CAP.VR
