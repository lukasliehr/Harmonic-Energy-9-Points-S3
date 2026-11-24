module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CAP.VR.Schema
public import CAP.VR.Layouts

/-!
# Virtual-root certificates: the theorem of the schema S4 for points of the sphere

`InPieceS P heads x e f` states the piece of a certificate for nine unit vectors `x` of `ℝ⁴` and two vectors
`e`, `f`: the pair `(e, f)` is orthonormal; `x 0 - x 1` is a multiple of `e` and `x 2 - x 3` lies in the plane of
`e` and `f` (the identities of the Gram–Schmidt frame); the coordinates `⟨x, e⟩`, `⟨x, f⟩` of the points satisfy
the inequalities of the cell lemma with the constants of the certificate, and the ring points the guards; the
inner product of every pair lies in the interval of its record type; the deviations are bounded.

`energy_gt`: if the labels, the identities and the bound of a certificate are checked, then

  `Bn / Bd < ∑ i < j, 1 / ‖x i - x j‖ ^ 2`

for every configuration of the piece. The proof completes `(e, f)` to an orthonormal basis of `ℝ⁴` and applies
the theorem in coordinates (`energy_coords`).

`checked_of`: the checked identities of a certificate from the lists of its records, minorants and labels.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)
open Finset

variable {P : Par} {heads : List RecH}

/-! ## The piece of a certificate -/

/-- The point with the label `l`. -/
noncomputable def pt (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (l : ℕ) : EuclideanSpace ℝ (Fin 4) :=
  if h : l < 9 then x ⟨l, h⟩ else 0

theorem pt_coe (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (i : Fin 9) : pt x i = x i := by
  unfold pt
  rw [dif_pos i.isLt]

/-- The deviation of the inner product of a pair with a point of the pair A or B from its linear part. -/
noncomputable def devS (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (e f : EuclideanSpace ℝ (Fin 4)) (i j : ℕ) : ℝ :=
  if i < 2 then
    (if j < 4 then inner ℝ (pt x i) (pt x j) - eps j * inner ℝ (pt x i) f - eps i * inner ℝ (pt x j) e
    else inner ℝ (pt x i) (pt x j) - eps i * inner ℝ (pt x j) e)
  else inner ℝ (pt x i) (pt x j) - eps i * inner ℝ (pt x j) f

/-- **The piece of a virtual-root certificate**: nine unit vectors `x` of `ℝ⁴`, labelled `a, a', b, b'` (the labels
`0, …, 3`) and `y₁, …, y₅` (the labels `4, …, 8`), with an orthonormal pair `(e, f)`. -/
structure InPieceS (P : Par) (heads : List RecH) (x : Fin 9 → EuclideanSpace ℝ (Fin 4))
    (e f : EuclideanSpace ℝ (Fin 4)) : Prop where
  unit : ∀ l, ‖x l‖ = 1
  eu : ‖e‖ = 1
  fu : ‖f‖ = 1
  ef : inner ℝ e f = 0
  frameA : x 0 - x 1 = (2 * inner ℝ (x 0) e) • e
  frameB : ∃ a b : ℝ, x 2 - x 3 = a • e + b • f
  pairA : ∀ l, l < 2 → PairPt P.cA P.mAP P.mAQ (eps l * inner ℝ (pt x l) e) (inner ℝ (pt x l) f)
    (1 - inner ℝ (pt x l) e ^ 2 - inner ℝ (pt x l) f ^ 2)
  pairB : ∀ l, 2 ≤ l → l < 4 → PairPt P.cB P.mBP P.mBQ (eps l * inner ℝ (pt x l) f) (inner ℝ (pt x l) e)
    (1 - inner ℝ (pt x l) e ^ 2 - inner ℝ (pt x l) f ^ 2)
  dir : (P.dird : ℝ) * (inner ℝ (pt x 2) e - inner ℝ (pt x 3) e) ^ 2
    ≤ P.dirn * (inner ℝ (pt x 2) f - inner ℝ (pt x 3) f) ^ 2
  ring : ∀ l, 4 ≤ l → l < 9 →
    (P.eR2d : ℝ) * inner ℝ (pt x l) e ^ 2 ≤ P.eR2n ∧ (P.eR2d : ℝ) * inner ℝ (pt x l) f ^ 2 ≤ P.eR2n
      ∧ (P.Gd : ℝ) * (inner ℝ (pt x l) e ^ 2 + inner ℝ (pt x l) f ^ 2) ≤ P.Gn
      ∧ (nth P.lowN (nth P.dcls l - 2) : ℝ)
        ≤ nth P.lowD (nth P.dcls l - 2) * (inner ℝ (pt x l) e ^ 2 + inner ℝ (pt x l) f ^ 2)
  iv : ∀ i j, i < j → j < 9 →
    ((hdOf P heads i j).lop : ℝ) - (hdOf P heads i j).lon ≤ (hdOf P heads i j).lod * inner ℝ (pt x i) (pt x j)
      ∧ (hdOf P heads i j).hid * inner ℝ (pt x i) (pt x j) ≤ ((hdOf P heads i j).hip : ℝ) - (hdOf P heads i j).hin
  sdev : ∀ i j, i < j → j < 9 → i < 4 → 2 ≤ j → (i < 2 ∨ 4 ≤ j) →
    ((hdOf P heads i j).aS2d : ℝ) * (2 ^ (hdOf P heads i j).mS * devS x e f i j) ^ 2 ≤ (hdOf P heads i j).aS2n

/-- The configuration in the coordinates of an orthonormal basis `e, f, g1, g2`. -/
noncomputable def confOf (x : Fin 9 → EuclideanSpace ℝ (Fin 4)) (e f g1 g2 : EuclideanSpace ℝ (Fin 4)) : Conf :=
  ⟨fun l => inner ℝ (pt x l) e, fun l => inner ℝ (pt x l) f, fun l => inner ℝ (pt x l) g1,
    fun l => inner ℝ (pt x l) g2⟩

theorem inPiece_of {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)}
    (h : InPieceS P heads x e f) (b : OrthonormalBasis (Fin 4) ℝ (EuclideanSpace ℝ (Fin 4))) (h0 : b 0 = e)
    (h1 : b 1 = f) :
    InPiece P heads (confOf x e f (b 2) (b 3))
      ∧ ∀ i j, (confOf x e f (b 2) (b 3)).t i j = inner ℝ (pt x i) (pt x j) := by
  -- the expansion of an inner product in the basis
  have hP : ∀ p q : EuclideanSpace ℝ (Fin 4), inner ℝ p q
      = inner ℝ p e * inner ℝ q e + inner ℝ p f * inner ℝ q f + inner ℝ p (b 2) * inner ℝ q (b 2)
        + inner ℝ p (b 3) * inner ℝ q (b 3) := by
    intro p q
    have hs := b.sum_inner_mul_inner p q
    rw [Fin.sum_univ_four, h0, h1] at hs
    rw [← hs, real_inner_comm q e, real_inner_comm q f, real_inner_comm q (b 2), real_inner_comm q (b 3)]
  have hT : ∀ i j, (confOf x e f (b 2) (b 3)).t i j = inner ℝ (pt x i) (pt x j) := fun i j => (hP _ _).symm
  have hon := orthonormal_iff_ite.mp b.orthonormal
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, h.eu, one_pow]
  have he2 : inner ℝ e (b 2) = 0 := by
    have := hon 0 2
    rw [h0] at this
    simpa using this
  have he3 : inner ℝ e (b 3) = 0 := by
    have := hon 0 3
    rw [h0] at this
    simpa using this
  have hf2 : inner ℝ f (b 2) = 0 := by
    have := hon 1 2
    rw [h1] at this
    simpa using this
  have hf3 : inner ℝ f (b 3) = 0 := by
    have := hon 1 3
    rw [h1] at this
    simpa using this
  have hunit : ∀ l, l < 9 → (confOf x e f (b 2) (b 3)).u l ^ 2 + (confOf x e f (b 2) (b 3)).v l ^ 2
      + (confOf x e f (b 2) (b 3)).ξ l ^ 2 + (confOf x e f (b 2) (b 3)).η l ^ 2 = 1 := by
    intro l hl
    have hn : ‖pt x l‖ = 1 := by
      unfold pt
      rw [dif_pos hl]
      exact h.unit _
    have hs := hP (pt x l) (pt x l)
    rw [real_inner_self_eq_norm_sq, hn, one_pow] at hs
    show inner ℝ (pt x l) e ^ 2 + inner ℝ (pt x l) f ^ 2 + inner ℝ (pt x l) (b 2) ^ 2 + inner ℝ (pt x l) (b 3) ^ 2 = 1
    rw [sq, sq, sq, sq]
    exact hs.symm
  have hR : ∀ l, l < 9 → (confOf x e f (b 2) (b 3)).R l = 1 - inner ℝ (pt x l) e ^ 2 - inner ℝ (pt x l) f ^ 2 := by
    intro l hl
    have hu := hunit l hl
    show inner ℝ (pt x l) (b 2) ^ 2 + inner ℝ (pt x l) (b 3) ^ 2 = _
    have hu' : inner ℝ (pt x l) e ^ 2 + inner ℝ (pt x l) f ^ 2 + inner ℝ (pt x l) (b 2) ^ 2
        + inner ℝ (pt x l) (b 3) ^ 2 = 1 := hu
    linarith
  -- the identities of the frame
  have p0 : pt x 0 = x 0 := pt_coe x 0
  have p1 : pt x 1 = x 1 := pt_coe x 1
  have p2 : pt x 2 = x 2 := pt_coe x 2
  have p3 : pt x 3 = x 3 := pt_coe x 3
  have hA : ∀ w : EuclideanSpace ℝ (Fin 4), inner ℝ (x 1) w = inner ℝ (x 0) w - 2 * inner ℝ (x 0) e * inner ℝ e w := by
    intro w
    have e1 : x 1 = x 0 - (2 * inner ℝ (x 0) e) • e := by
      rw [← h.frameA]
      abel
    rw [e1, inner_sub_left, real_inner_smul_left]
  obtain ⟨ca, cb, hB⟩ := h.frameB
  have hB' : ∀ w : EuclideanSpace ℝ (Fin 4), inner ℝ (x 3) w = inner ℝ (x 2) w - ca * inner ℝ e w - cb * inner ℝ f w := by
    intro w
    have e1 : x 3 = x 2 - (ca • e + cb • f) := by
      rw [← hB]
      abel
    rw [e1, inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  refine ⟨?_, hT⟩
  exact
    { unit := hunit
      frameA := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · show inner ℝ (pt x 1) e = -inner ℝ (pt x 0) e
          rw [p0, p1, hA e, hee]
          ring
        · show inner ℝ (pt x 1) f = inner ℝ (pt x 0) f
          rw [p0, p1, hA f, h.ef]
          ring
        · show inner ℝ (pt x 1) (b 2) = inner ℝ (pt x 0) (b 2)
          rw [p0, p1, hA (b 2), he2]
          ring
        · show inner ℝ (pt x 1) (b 3) = inner ℝ (pt x 0) (b 3)
          rw [p0, p1, hA (b 3), he3]
          ring
      frameB := by
        refine ⟨?_, ?_⟩
        · show inner ℝ (pt x 3) (b 2) = inner ℝ (pt x 2) (b 2)
          rw [p2, p3, hB' (b 2), he2, hf2]
          ring
        · show inner ℝ (pt x 3) (b 3) = inner ℝ (pt x 2) (b 3)
          rw [p2, p3, hB' (b 3), he3, hf3]
          ring
      pairA := fun l hl => by
        rw [hR l (by omega)]
        exact h.pairA l hl
      pairB := fun l hl2 hl => by
        rw [hR l (by omega)]
        exact h.pairB l hl2 hl
      dir := h.dir
      ring := h.ring
      iv := fun i j hij hj => by
        rw [hT]
        exact h.iv i j hij hj
      sdev := fun i j hij hj hi4 hj2 hor => by
        have hd : dev (confOf x e f (b 2) (b 3)) i j = devS x e f i j := by
          unfold dev devS
          rw [hT]
          rfl
        rw [hd]
        exact h.sdev i j hij hj hi4 hj2 hor }

/-! ## The energy -/

theorem sum_fin_pairs (n : ℕ) (g : ℕ → ℕ → ℝ) :
    ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j = ∑ j ∈ range n, ∑ i ∈ range j, g i j := by
  have h1 : ∀ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j
      = ∑ j ∈ range n, if (i : ℕ) < j then g i j else 0 := by
    intro i
    rw [Finset.sum_filter]
    exact Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) < j then g i j else 0) n
  calc ∑ i : Fin n, ∑ j ∈ univ.filter (fun j : Fin n => i < j), g i j
      = ∑ i : Fin n, ∑ j ∈ range n, if (i : ℕ) < j then g i j else 0 := Finset.sum_congr rfl fun i _ => h1 i
    _ = ∑ i ∈ range n, ∑ j ∈ range n, if i < j then g i j else 0 :=
      Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, if i < j then g i j else 0) n
    _ = ∑ j ∈ range n, ∑ i ∈ range n, if i < j then g i j else 0 := Finset.sum_comm
    _ = ∑ j ∈ range n, ∑ i ∈ range j, g i j := Finset.sum_congr rfl fun j hj => by
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      have := Finset.mem_range.1 hj
      omega

/-- **The theorem of the schema S4.** If the labels, the identities and the bound of a virtual-root certificate are
checked, then the energy of every configuration of its piece exceeds `Bn / Bd`. -/
theorem energy_gt {rl ml cl : List Loss} {gm : List ℕ} {F Bn Bd : ℕ} (hlab : labelsOk P heads = true)
    (hck : Checked P heads rl ml cl) (hb : boundOk P heads rl ml cl gm F Bn Bd = true)
    {x : Fin 9 → EuclideanSpace ℝ (Fin 4)} {e f : EuclideanSpace ℝ (Fin 4)} (hin : InPieceS P heads x e f) :
    (Bn : ℝ) / Bd < ∑ i, ∑ j ∈ univ.filter (fun j => i < j), 1 / ‖x i - x j‖ ^ 2 := by
  have hv : Orthonormal ℝ (({0, 1} : Set (Fin 4)).domRestrict ![e, f, 0, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · simp [Set.domRestrict, hin.eu]
    · simp [Set.domRestrict, hin.ef]
    · have : inner ℝ f e = 0 := by rw [real_inner_comm, hin.ef]
      simp [Set.domRestrict, this]
    · simp [Set.domRestrict, hin.fu]
  obtain ⟨b, hb'⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have h0 : b 0 = e := hb' 0 (by simp)
  have h1 : b 1 = f := hb' 1 (by simp)
  obtain ⟨hI, hT⟩ := inPiece_of hin b h0 h1
  have h := energy_coords hlab hck hb hI
  rw [← sum_fin_pairs 9 (fun i j => 1 / (2 - 2 * (confOf x e f (b 2) (b 3)).t i j))] at h
  refine lt_of_lt_of_eq h ?_
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hT, pt_coe, pt_coe, norm_sub_sq_real, hin.unit, hin.unit]
  congr 1
  ring

/-! ## The checked identities from lists -/

/-- The record identities of a list of record types, with their scales and norms. -/
def RecsOk (P : Par) : List RecH → List RecX → List Loss → Prop
  | [], _, _ => True
  | h :: hs, x :: xs, l :: ls =>
    (LayoutInj x.L ∧ recordOk P h x = true ∧ x.E = l.E ∧ x.rho = l.rho) ∧ RecsOk P hs xs ls
  | _ :: _, _, _ => False

/-- The minorant identities of a list of record types. -/
def MinosOk (P : Par) : List RecH → List MinoX → List Loss → Prop
  | [], _, _ => True
  | h :: hs, x :: xs, l :: ls =>
    (LayoutInj x.L ∧ minoOk P h x = true ∧ x.E = l.E ∧ x.rho = l.rho) ∧ MinosOk P hs xs ls
  | _ :: _, _, _ => False

/-- The identities of the labels `l, l + 1, …`. -/
def ClssOk (P : Par) (heads : List RecH) : ℕ → List ClsX → List Loss → Prop
  | _, [], _ => True
  | l, x :: xs, a :: as =>
    (LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l ∧ x.E = a.E ∧ x.rho = a.rho) ∧ ClssOk P heads (l + 1) xs as
  | _, _ :: _, [] => False

theorem recsOk_nth : ∀ (hs : List RecH) (xs : List RecX) (ls : List Loss), RecsOk P hs xs ls → ∀ k, k < lenH hs →
    ∃ x : RecX, LayoutInj x.L ∧ recordOk P (nthH hs k) x = true ∧ x.E = (nthLoss ls k).E ∧ x.rho = (nthLoss ls k).rho
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | _ :: _, _ :: _, [], hf, _, _ => False.elim hf
  | _ :: _, x :: _, _ :: _, hr, 0, _ => ⟨x, hr.1⟩
  | _ :: hs, _ :: xs, _ :: ls, hr, k + 1, hk => recsOk_nth hs xs ls hr.2 k (Nat.lt_of_succ_lt_succ hk)

theorem minosOk_nth : ∀ (hs : List RecH) (xs : List MinoX) (ls : List Loss), MinosOk P hs xs ls → ∀ k, k < lenH hs →
    ∃ x : MinoX, LayoutInj x.L ∧ minoOk P (nthH hs k) x = true ∧ x.E = (nthLoss ls k).E ∧ x.rho = (nthLoss ls k).rho
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | _ :: _, _ :: _, [], hf, _, _ => False.elim hf
  | _ :: _, x :: _, _ :: _, hr, 0, _ => ⟨x, hr.1⟩
  | _ :: hs, _ :: xs, _ :: ls, hr, k + 1, hk => minosOk_nth hs xs ls hr.2 k (Nat.lt_of_succ_lt_succ hk)

theorem clssOk_nth : ∀ (cs : List ClsX) (as : List Loss) (l0 : ℕ), ClssOk P heads l0 cs as → ∀ k, k < cs.length →
    ∃ x : ClsX, LayoutInj x.L ∧ clsOk P heads x = true ∧ x.label = l0 + k ∧ x.E = (nthLoss as k).E
      ∧ x.rho = (nthLoss as k).rho
  | [], _, _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | _ :: _, [], _, hf, _, _ => False.elim hf
  | x :: _, _ :: _, _, hr, 0, _ => ⟨x, hr.1⟩
  | _ :: cs, _ :: as, l0, hr, k + 1, hk => by
    obtain ⟨x, h1, h2, h3, h4⟩ := clssOk_nth cs as (l0 + 1) hr.2 k (Nat.lt_of_succ_lt_succ hk)
    exact ⟨x, h1, h2, by rw [h3]; omega, h4⟩

/-- **The checked identities of a certificate**, from the lists of its records, minorants and labels. -/
theorem checked_of {rl ml cl : List Loss} {xs : List RecX} {ms : List MinoX} {cs : List ClsX}
    (h1 : RecsOk P heads xs rl) (h2 : MinosOk P heads ms ml) (h3 : ClssOk P heads 0 cs cl) (h9 : cs.length = 9) :
    Checked P heads rl ml cl where
  recs := recsOk_nth heads xs rl h1
  minos := minosOk_nth heads ms ml h2
  clss := fun l hl => by
    obtain ⟨x, a, b, c, d⟩ := clssOk_nth cs cl 0 h3 l (by omega)
    exact ⟨x, a, b, by rw [c]; omega, d⟩

end CAP.VR
