module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Positivity
public import CAP.VR.Real

/-!
# Virtual-root certificates: configurations in coordinates, and the kernel

A labelled configuration is given by the coordinates `u = ⟨x, e⟩`, `v = ⟨x, f⟩` of its nine points in the
frame `(e, f)` and by the two coordinates `ξ`, `η` of the component `ζ` of a point in the orthogonal
complement of the plane of the frame. The labels `0, 1` are the points `a, a'` of the pair A, the labels
`2, 3` the points `b, b'` of the pair B, and the labels `4, …, 8` the ring points.

* `Kl P C l l'` is the kernel of the certificate between two labels: the sum over `k` of the two-root kernels
  `Re ((ζ ζ̄') ^ k)`, divided by `4 ^ (sK k)`, times the blocks `∑ columns, Ψ l * Ψ l'`. The sum of the kernel
  over all ordered pairs of labels is nonnegative (`Kl_psd`): for every column it is the square of the
  modulus of `∑ l, Ψ l * ζ l ^ k`.
* `piN` is the exchange value of a label towards another one.
* `InPiece` states the hypotheses on a configuration: unit vectors, the identities of the frame, the
  inequalities of the cell lemma that the weights use, the intervals of the record types and the guards.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open Finset

/-! ## The two-root kernels -/

theorem Qr_re (ω : ℂ) : ∀ k : ℕ, Qr (Complex.normSq ω) ω.re k = (ω ^ k).re
  | 0 => by simp [Qr]
  | 1 => by simp [Qr]
  | k + 2 => by
    have h1 := Qr_re ω (k + 1)
    have h0 := Qr_re ω k
    have h2 : ω ^ 2 = ((2 * ω.re : ℝ) : ℂ) * ω - ((Complex.normSq ω : ℝ) : ℂ) := by
      rw [← Complex.add_conj, ← Complex.mul_conj]
      ring
    have e : ω ^ (k + 2) = ((2 * ω.re : ℝ) : ℂ) * ω ^ (k + 1) - ((Complex.normSq ω : ℝ) : ℂ) * ω ^ k := by
      calc ω ^ (k + 2) = ω ^ k * ω ^ 2 := by ring
        _ = _ := by
          rw [h2]
          ring
    show 2 * ω.re * Qr (Complex.normSq ω) ω.re (k + 1) - Complex.normSq ω * Qr (Complex.normSq ω) ω.re k = _
    rw [h1, h0, e, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

theorem Qr_diag (ρ : ℝ) : ∀ k : ℕ, Qr (ρ * ρ) ρ k = ρ ^ k
  | 0 => by simp [Qr]
  | 1 => by simp [Qr]
  | k + 2 => by
    show 2 * ρ * Qr (ρ * ρ) ρ (k + 1) - ρ * ρ * Qr (ρ * ρ) ρ k = ρ ^ (k + 2)
    rw [Qr_diag ρ (k + 1), Qr_diag ρ k]
    ring

/-- A labelled configuration in coordinates. -/
structure Conf where
  u : ℕ → ℝ
  v : ℕ → ℝ
  ξ : ℕ → ℝ
  η : ℕ → ℝ

namespace Conf

variable (C : Conf)

/-- The inner product of two points. -/
noncomputable def t (i j : ℕ) : ℝ := C.u i * C.u j + C.v i * C.v j + C.ξ i * C.ξ j + C.η i * C.η j

/-- The square of the norm of `ζ`. -/
noncomputable def R (l : ℕ) : ℝ := C.ξ l ^ 2 + C.η l ^ 2

/-- The inner product of `ζ` and `ζ'`. -/
noncomputable def Hh (i j : ℕ) : ℝ := C.ξ i * C.ξ j + C.η i * C.η j

/-- `ζ` as a complex number. -/
noncomputable def z (l : ℕ) : ℂ := ⟨C.ξ l, C.η l⟩

theorem Hh_comm (i j : ℕ) : C.Hh i j = C.Hh j i := by
  unfold Hh
  ring

theorem Hh_self (l : ℕ) : C.Hh l l = C.R l := by
  unfold Hh R
  ring

theorem t_comm (i j : ℕ) : C.t i j = C.t j i := by
  unfold t
  ring

theorem Qr_eq (i j k : ℕ) :
    Qr (C.R i * C.R j) (C.Hh i j) k = ((C.z i * (starRingEnd ℂ) (C.z j)) ^ k).re := by
  rw [← Qr_re]
  congr 1
  · rw [Complex.normSq_mul, Complex.normSq_conj]
    simp only [z, Complex.normSq_mk, R]
    ring
  · simp only [z, Complex.mul_re, Complex.conj_re, Complex.conj_im, Hh]
    ring

theorem Qr_self (l k : ℕ) : Qr (C.R l * C.R l) (C.Hh l l) k = C.R l ^ k := by
  rw [Hh_self, Qr_diag]

theorem R_nonneg (l : ℕ) : 0 ≤ C.R l := by
  unfold R
  positivity

/-- **The kernels are positive semidefinite.** -/
theorem Qr_psd (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    0 ≤ ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * Qr (C.R l * C.R l') (C.Hh l l') k := by
  have e : ∀ l l', Qr (C.R l * C.R l') (C.Hh l l') k
      = (C.z l ^ k).re * (C.z l' ^ k).re + (C.z l ^ k).im * (C.z l' ^ k).im := by
    intro l l'
    rw [Qr_eq, mul_pow, ← map_pow, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h : ∑ l ∈ s, ∑ l' ∈ s, c l * c l' * Qr (C.R l * C.R l') (C.Hh l l') k
      = (∑ l ∈ s, c l * (C.z l ^ k).re) ^ 2 + (∑ l ∈ s, c l * (C.z l ^ k).im) ^ 2 := by
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [e]
    ring
  rw [h]
  positivity

end Conf

/-! ## The class coordinates of a label -/

/-- The sign of a label: `-1` for the second point of a pair. -/
noncomputable def eps (l : ℕ) : ℝ := if l = 1 ∨ l = 3 then -1 else 1

theorem eps_sq (l : ℕ) : eps l ^ 2 = 1 := by
  unfold eps
  split_ifs <;> norm_num

/-- The first class coordinate of a label. -/
noncomputable def cp (P : Par) (C : Conf) (l : ℕ) : ℝ :=
  if l < 2 then 2 ^ P.mAP * (1 - eps l * C.u l) else if l < 4 then 2 ^ P.mBP * (1 - eps l * C.v l) else C.u l

/-- The second class coordinate of a label. -/
noncomputable def cq (P : Par) (C : Conf) (l : ℕ) : ℝ :=
  if l < 2 then 2 ^ P.mAQ * C.v l else if l < 4 then 2 ^ P.mBQ * C.u l else C.v l

/-! ## The kernel between two labels -/

/-- The value of a column of a block of the kernel at a label. -/
noncomputable def Psi (P : Par) (C : Conf) (blk : Blk) (l col : ℕ) : ℝ :=
  sgnR (sgnOf (nth P.dcls l) (nth P.dsg l) blk)
    * psi blk (nth P.dcls l) (featL (nthL blk.ex (nth P.dcls l)) (cp P C l) (cq P C l)) col

/-- The blocks of one `k` between two labels. -/
noncomputable def Kb (P : Par) (C : Conf) (l l' : ℕ) (blks : List Blk) : ℝ :=
  (blks.map (fun blk => (blk.cols.map (fun col => Psi P C blk l col * Psi P C blk l' col)).sum)).sum

/-- **The kernel** of the certificate between two labels. -/
noncomputable def Kl (P : Par) (C : Conf) (l l' : ℕ) : ℝ :=
  kernR (Kb P C l l') (Qr (C.R l * C.R l') (C.Hh l l')) P.kblocks P.sK 0

theorem Kb_comm (P : Par) (C : Conf) (l l' : ℕ) (blks : List Blk) : Kb P C l l' blks = Kb P C l' l blks := by
  unfold Kb
  congr 1
  refine List.map_congr_left fun blk _ => ?_
  congr 1
  exact List.map_congr_left fun col _ => mul_comm _ _

theorem Kl_comm (P : Par) (C : Conf) (l l' : ℕ) : Kl P C l l' = Kl P C l' l := by
  unfold Kl
  refine kernR_congr (fun k => ?_) _ (fun blks _ => Kb_comm P C l l' blks) _ _
  rw [mul_comm, C.Hh_comm]

theorem list_psd {β : Type} (s : Finset ℕ) (w : ℕ → ℕ → ℝ) (g : β → ℕ → ℕ → ℝ)
    (h : ∀ b, 0 ≤ ∑ l ∈ s, ∑ l' ∈ s, w l l' * g b l l') :
    ∀ bs : List β, 0 ≤ ∑ l ∈ s, ∑ l' ∈ s, w l l' * (bs.map (fun b => g b l l')).sum
  | [] => by simp
  | b :: bs => by
    have e : ∑ l ∈ s, ∑ l' ∈ s, w l l' * ((b :: bs).map (fun b => g b l l')).sum
        = (∑ l ∈ s, ∑ l' ∈ s, w l l' * g b l l') + ∑ l ∈ s, ∑ l' ∈ s, w l l' * (bs.map (fun b => g b l l')).sum := by
      simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib]
    rw [e]
    exact add_nonneg (h b) (list_psd s w g h bs)

theorem Kb_psd (P : Par) (C : Conf) (s : Finset ℕ) (k n : ℕ) (blks : List Blk) :
    0 ≤ ∑ l ∈ s, ∑ l' ∈ s, Qr (C.R l * C.R l') (C.Hh l l') k / 4 ^ n * Kb P C l l' blks := by
  unfold Kb
  refine list_psd s _ (fun blk l l' => (blk.cols.map (fun col => Psi P C blk l col * Psi P C blk l' col)).sum)
    (fun blk => ?_) blks
  refine list_psd s _ (fun col l l' => Psi P C blk l col * Psi P C blk l' col) (fun col => ?_) blk.cols
  have e : ∑ l ∈ s, ∑ l' ∈ s, Qr (C.R l * C.R l') (C.Hh l l') k / 4 ^ n * (Psi P C blk l col * Psi P C blk l' col)
      = (∑ l ∈ s, ∑ l' ∈ s, Psi P C blk l col * Psi P C blk l' col * Qr (C.R l * C.R l') (C.Hh l l') k) / 4 ^ n := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring
  rw [e]
  exact div_nonneg (C.Qr_psd s (fun l => Psi P C blk l col) k) (by positivity)

/-- **The kernel is positive semidefinite**: its sum over all ordered pairs of labels is nonnegative. -/
theorem Kl_psd (P : Par) (C : Conf) (s : Finset ℕ) : 0 ≤ ∑ l ∈ s, ∑ l' ∈ s, Kl P C l l' := by
  unfold Kl
  generalize P.sK = sK
  generalize (0 : ℕ) = k
  induction P.kblocks generalizing sK k with
  | nil =>
    show 0 ≤ ∑ l ∈ s, ∑ l' ∈ s, (0 : ℝ)
    simp
  | cons blks rest ih =>
    have e : ∑ l ∈ s, ∑ l' ∈ s, kernR (Kb P C l l') (Qr (C.R l * C.R l') (C.Hh l l')) (blks :: rest) sK k
        = (∑ l ∈ s, ∑ l' ∈ s, Qr (C.R l * C.R l') (C.Hh l l') k / 4 ^ hd sK * Kb P C l l' blks)
          + ∑ l ∈ s, ∑ l' ∈ s, kernR (Kb P C l l') (Qr (C.R l * C.R l') (C.Hh l l')) rest (tl sK) (k + 1) := by
      simp only [kernR, Finset.sum_add_distrib]
    rw [e]
    exact add_nonneg (Kb_psd P C s k (hd sK) blks) (ih (tl sK) (k + 1))

/-! ## The exchange values -/

/-- The record type of a pair `i < j` of labels. -/
noncomputable def hdOf (P : Par) (heads : List RecH) (i j : ℕ) : RecH := nthH heads (nth P.rt (pairIndex i j))

theorem headOf_lt {P : Par} {heads : List RecH} {i j : ℕ} (h : i < j) : headOf P heads i j = hdOf P heads i j := by
  have hb : Nat.blt i j = true := by
    rw [Nat.blt_eq]
    exact h
  unfold headOf hdOf
  rw [hb]
  rfl

theorem headOf_gt {P : Par} {heads : List RecH} {i j : ℕ} (h : i < j) : headOf P heads j i = hdOf P heads i j := by
  have hb : Nat.blt j i = false := by
    cases hbb : Nat.blt j i
    · rfl
    · exact absurd (lt_of_blt hbb) (by omega)
  unfold headOf hdOf
  rw [hb]
  rfl

/-- The signs of the class coordinates of the label `l` in the data of its pair with the label `o`. -/
noncomputable def fP (l o : ℕ) : ℝ := (-1) ^ flipP l o

noncomputable def fQ (l o : ℕ) : ℝ := (-1) ^ flipQ l o

theorem flipP_lt (l o : ℕ) : flipP l o < 2 := by
  unfold flipP
  cases (Nat.ble 4 l && Nat.beq o 1) <;> decide

theorem flipQ_lt (l o : ℕ) : flipQ l o < 2 := by
  unfold flipQ
  cases ((Nat.ble l 1 && Nat.beq o 3) || (Nat.ble 2 l && Nat.ble l 3 && Nat.beq o 1) || (Nat.ble 4 l && Nat.beq o 3)) <;>
    decide

/-- **The exchange value** of the label `l` towards the label `o`, in the unit `2 ^ -sP`. -/
noncomputable def piN (P : Par) (heads : List RecH) (C : Conf) (l o : ℕ) : ℝ :=
  if l < o then
    poly2 P.wP (headOf P heads l o).p1ex (headOf P heads l o).p1p (headOf P heads l o).p1n
      (fP l o * cp P C l) (fQ l o * cq P C l)
  else
    poly2 P.wP (headOf P heads l o).p2ex (headOf P heads l o).p2p (headOf P heads l o).p2n
      (fP l o * cp P C l) (fQ l o * cq P C l)

/-! ## Lists of record types -/

/-- The record type beyond the end of a list. -/
def RecH.none : RecH :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, [], 0, 0, [], 0, 0, 0, 0, 0, [], 0, 0, 0, 0, 0, 0, 0, 0⟩

theorem nthH_mem : ∀ (l : List RecH) (k : ℕ), k < lenH l → nthH l k ∈ l
  | [], k, h => absurd h (Nat.not_lt_zero k)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, k + 1, h => List.mem_cons_of_mem _ (nthH_mem l k (Nat.lt_of_succ_lt_succ h))

theorem allH_mem {f : RecH → Bool} : ∀ (l : List RecH), allH f l = true → ∀ h ∈ l, f h = true
  | [], _, h, hm => by simp at hm
  | a :: l, hall, h, hm => by
    have h' : (f a && allH f l) = true := hall
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h'.1
    · exact allH_mem l h'.2 h hm

theorem allN_lt {f : ℕ → Bool} : ∀ (n : ℕ), allN f n = true → ∀ k, k < n → f k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | n + 1, h, k, hk => by
    have h' : (allN f n && f n) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact allN_lt n h'.1 k hk
    · exact h'.2

/-! ## The hypotheses on a configuration -/

/-- A point of a pair with the major coordinate `M`, the minor coordinate `N` and `Rv = |ζ|²`: the
inequalities of the cell lemma that the weights of its class use. -/
structure PairPt (c : PairConst) (mP mQ : ℕ) (M N Rv : ℝ) : Prop where
  major : (c.aPd : ℝ) * (2 ^ mP * (1 - M)) ≤ c.aPn
  minor : (c.aQ2d : ℝ) * (2 ^ mQ * N) ^ 2 ≤ c.aQ2n
  eta : (c.etad : ℝ) * Rv ≤ c.etan
  cone : (c.td : ℝ) * N ^ 2 ≤ c.tn * M ^ 2
  gs : (c.g1 : ℝ) * Rv + c.g2 * N ^ 2 ≤ c.g0

/-- The deviation of the inner product of a pair with a point of the pair A or B from its linear part. -/
noncomputable def dev (C : Conf) (i j : ℕ) : ℝ :=
  if i < 2 then (if j < 4 then C.t i j - eps j * C.v i - eps i * C.u j else C.t i j - eps i * C.u j)
  else C.t i j - eps i * C.v j

/-- **The piece of a certificate**, in coordinates: the points are unit vectors; the identities of the
Gram–Schmidt frame hold (`u a' = -u a`, `v a' = v a`, `ζ a' = ζ a`, `ζ b' = ζ b`); the points of the pairs and
of the ring satisfy the inequalities of the cell lemma with the constants of the certificate, and the ring
points the guards; the inner product of every pair lies in the interval of its record type; and the
deviations are bounded. -/
structure InPiece (P : Par) (heads : List RecH) (C : Conf) : Prop where
  unit : ∀ l, l < 9 → C.u l ^ 2 + C.v l ^ 2 + C.ξ l ^ 2 + C.η l ^ 2 = 1
  frameA : C.u 1 = -C.u 0 ∧ C.v 1 = C.v 0 ∧ C.ξ 1 = C.ξ 0 ∧ C.η 1 = C.η 0
  frameB : C.ξ 3 = C.ξ 2 ∧ C.η 3 = C.η 2
  pairA : ∀ l, l < 2 → PairPt P.cA P.mAP P.mAQ (eps l * C.u l) (C.v l) (C.R l)
  pairB : ∀ l, 2 ≤ l → l < 4 → PairPt P.cB P.mBP P.mBQ (eps l * C.v l) (C.u l) (C.R l)
  dir : (P.dird : ℝ) * (C.u 2 - C.u 3) ^ 2 ≤ P.dirn * (C.v 2 - C.v 3) ^ 2
  ring : ∀ l, 4 ≤ l → l < 9 →
    (P.eR2d : ℝ) * C.u l ^ 2 ≤ P.eR2n ∧ (P.eR2d : ℝ) * C.v l ^ 2 ≤ P.eR2n
      ∧ (P.Gd : ℝ) * (C.u l ^ 2 + C.v l ^ 2) ≤ P.Gn
      ∧ (nth P.lowN (nth P.dcls l - 2) : ℝ) ≤ nth P.lowD (nth P.dcls l - 2) * (C.u l ^ 2 + C.v l ^ 2)
  iv : ∀ i j, i < j → j < 9 →
    ((hdOf P heads i j).lop : ℝ) - (hdOf P heads i j).lon ≤ (hdOf P heads i j).lod * C.t i j
      ∧ (hdOf P heads i j).hid * C.t i j ≤ ((hdOf P heads i j).hip : ℝ) - (hdOf P heads i j).hin
  sdev : ∀ i j, i < j → j < 9 → i < 4 → 2 ≤ j → (i < 2 ∨ 4 ≤ j) →
    ((hdOf P heads i j).aS2d : ℝ) * (2 ^ (hdOf P heads i j).mS * dev C i j) ^ 2 ≤ (hdOf P heads i j).aS2n

end CAP.VR
