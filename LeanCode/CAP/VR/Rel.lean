module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.List.Forall2
public import CAP.VR.Kernel

/-!
# Virtual-root certificates: related sets of operations give related values

The functions of the checker are defined for an arbitrary set of operations. `OpsRel R G A B` states that a
relation `R` between the values of two sets of operations `A`, `B` is compatible with the operations
(for the squares of a block under the condition `G` on the block). Then `R` relates the values of every
function of the checker: `recVal_rel`, `minoVal_rel`, `clsVal_rel`, and `recValX_rel`, `minoValX_rel` for the
identities with exact parts. The proofs follow the definitions.
-/

@[expose] public section

namespace CAP.VR

open CAP.Wsos (nth hd tl len)

variable {α β : Type} {R : α → β → Prop} {G : ℕ → ℕ → ℕ → ℕ → Prop} {A : Ops α} {B : Ops β}

/-- The relation `R` is compatible with the operations of `A` and `B`. -/
structure OpsRel (R : α → β → Prop) (G : ℕ → ℕ → ℕ → ℕ → Prop) (A : Ops α) (B : Ops β) : Prop where
  add : ∀ {a a' b b'}, R a b → R a' b' → R (A.add a a') (B.add b b')
  sub : ∀ {a a' b b'}, R a b → R a' b' → R (A.sub a a') (B.sub b b')
  mul : ∀ {a a' b b'}, R a b → R a' b' → R (A.mul a a') (B.mul b b')
  smul : ∀ (n : ℕ) {a b}, R a b → R (A.smul n a) (B.smul n b)
  nat : ∀ n : ℕ, R (A.nat n) (B.nat n)
  mono : ∀ c : ℕ, R (A.mono c) (B.mono c)
  sq : ∀ δ dp cls wb col r, G δ dp cls wb → R (A.sq δ dp cls wb col r) (B.sq δ dp cls wb col r)
  dg : ∀ δ dp cls wb d, G δ dp cls wb → R (A.dg δ dp cls wb d) (B.dg δ dp cls wb d)

theorem cond_rel {γ δ : Type} {S : γ → δ → Prop} {b : Bool} {x y : γ} {x' y' : δ} (h1 : S x x') (h2 : S y y') :
    S (cond b x y) (cond b x' y') := by
  cases b
  · exact h2
  · exact h1

theorem forall₂_append {l1 l2 : List α} {l1' l2' : List β} (h1 : List.Forall₂ R l1 l1') (h2 : List.Forall₂ R l2 l2') :
    List.Forall₂ R (l1 ++ l2) (l1' ++ l2') := by
  induction h1 with
  | nil => exact h2
  | cons a _ ih => exact List.Forall₂.cons a ih

section

variable (h : OpsRel R G A B)
include h

theorem var_rel (i : ℕ) : R (var A i) (var B i) := h.mono _

theorem sqr_rel {a : α} {b : β} (hab : R a b) : R (sqr A a) (sqr B b) := h.mul hab hab

theorem hdA_rel {l : List α} {l' : List β} (hl : List.Forall₂ R l l') : R (hdA A l) (hdA B l') := by
  cases hl with
  | nil => exact h.nat 0
  | cons h1 _ => exact h1

omit h in
theorem tlA_rel {l : List α} {l' : List β} (hl : List.Forall₂ R l l') : List.Forall₂ R (tlA l) (tlA l') := by
  cases hl with
  | nil => exact List.Forall₂.nil
  | cons _ h2 => exact h2

theorem monoListAt_rel (ip iq : ℕ) : ∀ l : List ℕ, List.Forall₂ R (monoListAt A ip iq l) (monoListAt B ip iq l)
  | [] => List.Forall₂.nil
  | _ :: l => List.Forall₂.cons (h.mono _) (monoListAt_rel ip iq l)

theorem lsumG_rel {l : List α} {l' : List β} (hl : List.Forall₂ R l l') : R (lsumG A l) (lsumG B l') := by
  induction hl with
  | nil => exact h.nat 0
  | cons h1 _ ih => exact h.add h1 ih

theorem dot_rel (w mw : ℕ) {ms : List α} {ms' : List β} (hl : List.Forall₂ R ms ms') :
    ∀ (N : ℕ) {U : α} {U' : β}, R U U' → R (dot A w mw ms N U) (dot B w mw ms' N U') := by
  induction hl with
  | nil => exact fun _ _ _ hU => hU
  | cons h1 _ ih => exact fun _ _ _ hU => ih _ (h.add hU (h.smul _ h1))

omit h in
theorem dotGo_cons (o : Ops α) (w mw : ℕ) (cf : ℕ → ℕ) (fl : ℕ → Bool) (c : ℕ) (l : List ℕ) (Np Nn : ℕ) (P N : α) :
    dotGo o w mw cf fl (c :: l) Np Nn P N
      = cond (fl c)
        (dotGo o w mw cf fl l (Nat.shiftRight Np w) (Nat.shiftRight Nn w) (o.add P (o.smul (Nat.land Nn mw) (o.mono (cf c))))
          (o.add N (o.smul (Nat.land Np mw) (o.mono (cf c)))))
        (dotGo o w mw cf fl l (Nat.shiftRight Np w) (Nat.shiftRight Nn w) (o.add P (o.smul (Nat.land Np mw) (o.mono (cf c))))
          (o.add N (o.smul (Nat.land Nn mw) (o.mono (cf c))))) := rfl

theorem dotGo_rel (w mw : ℕ) (cf : ℕ → ℕ) (fl : ℕ → Bool) :
    ∀ (codes : List ℕ) (Np Nn : ℕ) {P N : α} {P' N' : β}, R P P' → R N N' →
      R (dotGo A w mw cf fl codes Np Nn P N) (dotGo B w mw cf fl codes Np Nn P' N')
  | [], _, _, _, _, _, _, hP, hN => h.sub hP hN
  | c :: l, Np, Nn, _, _, _, _, hP, hN => by
    rw [dotGo_cons, dotGo_cons]
    exact cond_rel (dotGo_rel w mw cf fl l _ _ (h.add hP (h.smul _ (h.mono _))) (h.add hN (h.smul _ (h.mono _))))
      (dotGo_rel w mw cf fl l _ _ (h.add hP (h.smul _ (h.mono _))) (h.add hN (h.smul _ (h.mono _))))

theorem dotS_rel (w tp tq ip iq : ℕ) (codes : List ℕ) (Np Nn : ℕ) :
    R (dotS A w tp tq ip iq codes Np Nn) (dotS B w tp tq ip iq codes Np Nn) :=
  dotGo_rel h _ _ _ _ _ _ _ (h.nat 0) (h.nat 0)

theorem dot5_rel (w : ℕ) (codes : List ℕ) (Np Nn : ℕ) : R (dot5 A w codes Np Nn) (dot5 B w codes Np Nn) :=
  dotGo_rel h _ _ _ _ _ _ _ (h.nat 0) (h.nat 0)

/-! ### The classes and the geometry -/

theorem clsMaj_rel (P : Par) (cls ip : ℕ) : R (clsMaj A P cls ip) (clsMaj B P cls ip) :=
  h.sub (h.nat _) (h.smul _ (var_rel h _))

theorem clsMin_rel (P : Par) (cls iq : ℕ) : R (clsMin A P cls iq) (clsMin B P cls iq) := h.smul _ (var_rel h _)

theorem signed_rel (sg : ℕ) {a : α} {b : β} (hab : R a b) : R (signed A sg a) (signed B sg b) :=
  cond_rel (h.sub (h.nat 0) hab) hab

theorem clsU_rel (P : Par) (cls sg ip iq : ℕ) : R (clsU A P cls sg ip iq) (clsU B P cls sg ip iq) :=
  cond_rel (signed_rel h _ (clsMaj_rel h _ _ _)) (cond_rel (clsMin_rel h _ _ _) (var_rel h _))

theorem clsV_rel (P : Par) (cls sg ip iq : ℕ) : R (clsV A P cls sg ip iq) (clsV B P cls sg ip iq) :=
  cond_rel (clsMin_rel h _ _ _) (cond_rel (signed_rel h _ (clsMaj_rel h _ _ _)) (var_rel h _))

theorem clsR_rel (m : ℕ) {U V : α} {U' V' : β} (hU : R U U') (hV : R V V') : R (clsR A m U V) (clsR B m U' V') :=
  h.sub (h.nat _) (h.add (sqr_rel h hU) (sqr_rel h hV))

theorem recT_rel (P : Par) (hd : RecH) {U1 V1 U2 V2 : α} {U1' V1' U2' V2' : β} (h1 : R U1 U1') (h2 : R V1 V1')
    (h3 : R U2 U2') (h4 : R V2 V2') : R (recT A P hd U1 V1 U2 V2) (recT B P hd U1' V1' U2' V2') := by
  unfold recT
  refine cond_rel (h.sub (h.nat _) (h.smul _ (sqr_rel h h1))) (cond_rel ?_ (cond_rel ?_ (cond_rel ?_ (cond_rel ?_ ?_))))
  · exact h.sub (h.nat _) (h.add (sqr_rel h (h.sub h1 h3)) (sqr_rel h (h.sub h2 h4)))
  · exact h.add (h.smul _ (var_rel h _)) (h.add (h.smul _ h2) (h.smul _ h3))
  · exact h.add (var_rel h _) (h.smul _ h3)
  · exact h.add (var_rel h _) (h.smul _ h4)
  · exact h.sub (h.add (h.nat _) (h.smul _ (var_rel h _))) (h.nat _)

theorem recHv_rel (m1 m2 mT : ℕ) {U1 V1 U2 V2 T : α} {U1' V1' U2' V2' T' : β} (h1 : R U1 U1') (h2 : R V1 V1')
    (h3 : R U2 U2') (h4 : R V2 V2') (h5 : R T T') :
    R (recHv A m1 m2 mT U1 V1 U2 V2 T) (recHv B m1 m2 mT U1' V1' U2' V2' T') :=
  h.sub (h.smul _ h5) (h.smul _ (h.add (h.mul h1 h3) (h.mul h2 h4)))

omit h in
theorem qGo_succ (o : Ops α) (H Wt : α) (mT n k : ℕ) (prev cur : α) :
    qGo o H Wt mT (n + 1) k prev cur = cur :: qGo o H Wt mT n (Nat.succ k) cur
      (cond (Nat.beq k 0) H (o.sub (o.smul 2 (o.mul H cur)) (o.smul (Nat.shiftLeft 1 (Nat.mul 2 mT)) (o.mul Wt prev)))) := rfl

theorem qGo_rel {H Wt : α} {H' Wt' : β} (hH : R H H') (hW : R Wt Wt') (mT : ℕ) :
    ∀ (n k : ℕ) {prev cur : α} {prev' cur' : β}, R prev prev' → R cur cur' →
      List.Forall₂ R (qGo A H Wt mT n k prev cur) (qGo B H' Wt' mT n k prev' cur')
  | 0, _, _, _, _, _, _, _ => List.Forall₂.nil
  | n + 1, k, _, _, _, _, hp, hc => by
    rw [qGo_succ, qGo_succ]
    exact List.Forall₂.cons hc (qGo_rel hH hW mT n _ hc
      (cond_rel hH (h.sub (h.smul _ (h.mul hH hc)) (h.smul _ (h.mul hW hp)))))

theorem qList_rel {H Wt : α} {H' Wt' : β} (hH : R H H') (hW : R Wt Wt') (mT n : ℕ) :
    List.Forall₂ R (qList A H Wt mT n) (qList B H' Wt' mT n) :=
  qGo_rel h hH hW mT n 0 (h.nat 0) (h.nat 1)

/-! ### The kernel -/

/-- The relation of three values. -/
def R3 (R : α → β → Prop) (x : α × α × α) (y : β × β × β) : Prop := R x.1 y.1 ∧ R x.2.1 y.2.1 ∧ R x.2.2 y.2.2

omit h in
theorem colsGo_cons (o : Ops α) (wb mw : ℕ) (ms1 ms2 : List α) (o1 o2 col : ℕ) (l : List ℕ) :
    colsGo o wb mw ms1 ms2 o1 o2 (col :: l)
      = (o.add (colsGo o wb mw ms1 ms2 o1 o2 l).1
            (o.mul (dot o wb mw ms1 (Nat.shiftRight col o1) (o.nat 0)) (dot o wb mw ms2 (Nat.shiftRight col o2) (o.nat 0))),
          o.add (colsGo o wb mw ms1 ms2 o1 o2 l).2.1 (dot o wb mw ms1 (Nat.shiftRight col o1) (o.nat 0)),
          o.add (colsGo o wb mw ms1 ms2 o1 o2 l).2.2 (dot o wb mw ms2 (Nat.shiftRight col o2) (o.nat 0))) := rfl

theorem colsGo_rel (wb mw : ℕ) {ms1 ms2 : List α} {ms1' ms2' : List β} (h1 : List.Forall₂ R ms1 ms1')
    (h2 : List.Forall₂ R ms2 ms2') (o1 o2 : ℕ) :
    ∀ l : List ℕ, R3 R (colsGo A wb mw ms1 ms2 o1 o2 l) (colsGo B wb mw ms1' ms2' o1 o2 l)
  | [] => ⟨h.nat 0, h.nat 0, h.nat 0⟩
  | col :: l => by
    rw [colsGo_cons, colsGo_cons]
    obtain ⟨a, b, c⟩ := colsGo_rel wb mw h1 h2 o1 o2 l
    exact ⟨h.add a (h.mul (dot_rel h _ _ h1 _ (h.nat 0)) (dot_rel h _ _ h2 _ (h.nat 0))),
      h.add b (dot_rel h _ _ h1 _ (h.nat 0)), h.add c (dot_rel h _ _ h2 _ (h.nat 0))⟩

theorem blkBil_rel (blk : Blk) (c1 i1p i1q c2 i2p i2q : ℕ) :
    R (blkBil A blk c1 i1p i1q c2 i2p i2q) (blkBil B blk c1 i1p i1q c2 i2p i2q) := by
  unfold blkBil
  refine cond_rel (h.nat 0) ?_
  obtain ⟨a, b, c⟩ := colsGo_rel h blk.wb (mask blk.wb) (monoListAt_rel h i1p i1q (nthL blk.ex c1))
    (monoListAt_rel h i2p i2q (nthL blk.ex c2)) (Nat.mul blk.wb (nth blk.off c1)) (Nat.mul blk.wb (nth blk.off c2)) blk.cols
  have s1 := lsumG_rel h (monoListAt_rel h i1p i1q (nthL blk.ex c1))
  have s2 := lsumG_rel h (monoListAt_rel h i2p i2q (nthL blk.ex c2))
  exact h.sub (h.add a (h.smul _ (h.mul s1 s2))) (h.smul _ (h.add (h.mul b s2) (h.mul s1 c)))

omit h in
theorem innerK_cons (o : Ops α) (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) (blk : Blk) (l : List Blk) (acc : α) :
    innerK o c1 s1 i1p i1q c2 s2 i2p i2q (blk :: l) acc
      = innerK o c1 s1 i1p i1q c2 s2 i2p i2q l
        (cond (Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 0) acc
          (cond (Nat.beq (sgnMul (sgnOf c1 s1 blk) (sgnOf c2 s2 blk)) 1)
            (o.add acc (blkBil o blk c1 i1p i1q c2 i2p i2q)) (o.sub acc (blkBil o blk c1 i1p i1q c2 i2p i2q)))) := rfl

theorem innerK_rel (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) :
    ∀ (l : List Blk) {acc : α} {acc' : β}, R acc acc' →
      R (innerK A c1 s1 i1p i1q c2 s2 i2p i2q l acc) (innerK B c1 s1 i1p i1q c2 s2 i2p i2q l acc')
  | [], _, _, ha => ha
  | blk :: l, _, _, ha => by
    rw [innerK_cons, innerK_cons]
    exact innerK_rel c1 s1 i1p i1q c2 s2 i2p i2q l
      (cond_rel ha (cond_rel (h.add ha (blkBil_rel h _ _ _ _ _ _ _)) (h.sub ha (blkBil_rel h _ _ _ _ _ _ _))))

omit h in
theorem kernGo_cons (o : Ops α) (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) (blks : List Blk) (l : List (List Blk)) (qs : List α)
    (aK : List ℕ) (acc : α) :
    kernGo o c1 s1 i1p i1q c2 s2 i2p i2q (blks :: l) qs aK acc
      = kernGo o c1 s1 i1p i1q c2 s2 i2p i2q l (tlA qs) (tl aK)
        (cond (usedK c1 c2 blks)
          (o.add acc (o.smul (Nat.shiftLeft 1 (hd aK)) (o.mul (hdA o qs) (innerK o c1 s1 i1p i1q c2 s2 i2p i2q blks (o.nat 0)))))
          acc) := rfl

theorem kernGo_rel (c1 s1 i1p i1q c2 s2 i2p i2q : ℕ) :
    ∀ (l : List (List Blk)) {qs : List α} {qs' : List β} (aK : List ℕ) {acc : α} {acc' : β}, List.Forall₂ R qs qs' →
      R acc acc' → R (kernGo A c1 s1 i1p i1q c2 s2 i2p i2q l qs aK acc) (kernGo B c1 s1 i1p i1q c2 s2 i2p i2q l qs' aK acc')
  | [], _, _, _, _, _, _, ha => ha
  | blks :: l, _, _, aK, _, _, hq, ha => by
    rw [kernGo_cons, kernGo_cons]
    exact kernGo_rel c1 s1 i1p i1q c2 s2 i2p i2q l _ (tlA_rel hq)
      (cond_rel (h.add ha (h.smul _ (h.mul (hdA_rel h hq) (innerK_rel h _ _ _ _ _ _ _ _ _ (h.nat 0))))) ha)

/-! ### The minorant inside a record -/

omit h in
theorem hornerGo_succ (o : Ops α) (w mw hp hn : ℕ) (that : α) (mH r i : ℕ) (acc : α) :
    hornerGo o w mw hp hn that mH (r + 1) i acc
      = hornerGo o w mw hp hn that mH r (Nat.succ i)
        (o.add (o.mul acc that)
          (o.smul (Nat.shiftLeft 1 (Nat.mul mH i))
            (o.sub (o.nat (Nat.land (Nat.shiftRight hp (Nat.mul w r)) mw))
              (o.nat (Nat.land (Nat.shiftRight hn (Nat.mul w r)) mw))))) := rfl

theorem hornerGo_rel (w mw hp hn : ℕ) {that : α} {that' : β} (ht : R that that') (mH : ℕ) :
    ∀ (r i : ℕ) {acc : α} {acc' : β}, R acc acc' →
      R (hornerGo A w mw hp hn that mH r i acc) (hornerGo B w mw hp hn that' mH r i acc')
  | 0, _, _, _, ha => ha
  | r + 1, i, _, _, ha => by
    rw [hornerGo_succ, hornerGo_succ]
    exact hornerGo_rel w mw hp hn ht mH r _ (h.add (h.mul ha ht) (h.smul _ (h.sub (h.nat _) (h.nat _))))

theorem recThat_rel (hd : RecH) {T : α} {T' : β} (hT : R T T') (mT : ℕ) : R (recThat A hd T mT) (recThat B hd T' mT) :=
  h.smul _ (h.sub (h.add (h.smul _ hT) (h.nat _)) (h.nat _))

theorem recHm_rel (P : Par) (hd : RecH) {T : α} {T' : β} (hT : R T T') (mT : ℕ) :
    R (recHm A P hd T mT) (recHm B P hd T' mT) :=
  cond_rel (dotS_rel h _ _ _ _ _ _ _ _) (hornerGo_rel h _ _ _ _ (recThat_rel h hd hT mT) _ _ _ (h.nat 0))

/-! ### The localizers -/

theorem locPair_rel (P : Par) (cls ip iq : ℕ) {Rv : α} {Rv' : β} (hR : R Rv Rv') (m : ℕ) :
    List.Forall₂ R (locPair A P cls ip iq Rv m) (locPair B P cls ip iq Rv' m) := by
  unfold locPair
  have hmaj := clsMaj_rel h P cls ip
  have hmin := sqr_rel h (clsMin_rel h P cls iq)
  exact List.Forall₂.cons hR (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ hR))
    (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (var_rel h _)))
      (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (sqr_rel h (var_rel h _))))
        (List.Forall₂.cons (h.sub (h.smul _ (sqr_rel h hmaj)) (h.smul _ hmin))
          (List.Forall₂.cons (h.sub (h.nat _) (h.add (h.smul _ hR) (h.smul _ hmin))) List.Forall₂.nil)))))

theorem locRing_rel (P : Par) (cls ip iq : ℕ) {Rv : α} {Rv' : β} (hR : R Rv Rv') :
    List.Forall₂ R (locRing A P cls ip iq Rv) (locRing B P cls ip iq Rv') := by
  unfold locRing
  have hp := sqr_rel h (var_rel h ip)
  have hq := sqr_rel h (var_rel h iq)
  exact List.Forall₂.cons hR (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ hp))
    (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ hq))
      (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (h.add hp hq)))
        (List.Forall₂.cons (h.sub (h.smul _ (h.add hp hq)) (h.nat _)) List.Forall₂.nil))))

theorem locEnd_rel (P : Par) (cls ip iq : ℕ) {Rv : α} {Rv' : β} (hR : R Rv Rv') (m : ℕ) :
    List.Forall₂ R (locEnd A P cls ip iq Rv m) (locEnd B P cls ip iq Rv' m) :=
  cond_rel (locPair_rel h P cls ip iq hR m) (locRing_rel h P cls ip iq hR)

theorem locT_rel (hd : RecH) {T : α} {T' : β} (hT : R T T') (mT : ℕ) : R (locT A hd T mT) (locT B hd T' mT) :=
  h.mul (h.sub (h.add (h.smul _ hT) (h.nat _)) (h.nat _)) (h.sub (h.nat _) (h.add (h.smul _ hT) (h.nat _)))

theorem locG3_rel {A1 A2 T : α} {A1' A2' T' : β} (h1 : R A1 A1') (h2 : R A2 A2') (hT : R T T') (m1 m2 mT : ℕ) :
    R (locG3 A A1 A2 T m1 m2 mT) (locG3 B A1' A2' T' m1 m2 mT) :=
  h.sub (h.add (h.nat _) (h.smul _ (h.mul (h.mul h1 h2) hT)))
    (h.add (h.add (h.smul _ (sqr_rel h h1)) (h.smul _ (sqr_rel h h2))) (h.smul _ (sqr_rel h hT)))

theorem recLocs_rel (P : Par) (hd : RecH) (i2p i2q m1 m2 mT : ℕ) {U1 V1 U2 V2 T R1 R2 H Wt : α}
    {U1' V1' U2' V2' T' R1' R2' H' Wt' : β} (hU1 : R U1 U1') (hV1 : R V1 V1') (hU2 : R U2 U2') (hV2 : R V2 V2')
    (hT : R T T') (hR1 : R R1 R1') (hR2 : R R2 R2') (hH : R H H') (hW : R Wt Wt') :
    List.Forall₂ R (recLocs A P hd i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2 H Wt)
      (recLocs B P hd i2p i2q m1 m2 mT U1' V1' U2' V2' T' R1' R2' H' Wt') := by
  unfold recLocs
  refine List.Forall₂.cons (h.nat 1) (forall₂_append (locEnd_rel h P _ _ _ hR1 m1)
    (forall₂_append (cond_rel List.Forall₂.nil (locEnd_rel h P _ _ _ hR2 m2))
      (List.Forall₂.cons (locT_rel h hd hT mT)
        (forall₂_append (cond_rel (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (sqr_rel h (var_rel h 4)))) List.Forall₂.nil)
            List.Forall₂.nil)
          (List.Forall₂.cons (locG3_rel h hU1 hU2 hT m1 m2 mT) (List.Forall₂.cons (locG3_rel h hV1 hV2 hT m1 m2 mT)
            (forall₂_append (cond_rel (List.Forall₂.cons (h.sub (h.smul _ hW) (sqr_rel h hH)) List.Forall₂.nil) List.Forall₂.nil)
              (cond_rel (List.Forall₂.cons
                (h.sub (h.smul _ (sqr_rel h (h.sub hV1 hV2))) (h.smul _ (sqr_rel h (h.sub hU1 hU2)))) List.Forall₂.nil)
                List.Forall₂.nil))))))))

/-! ### The sums of squares -/

/-- All blocks of a list satisfy the condition of the relation. -/
def BlocksG (G : ℕ → ℕ → ℕ → ℕ → Prop) : List WBlk → Prop
  | [] => True
  | b :: l => G b.delta b.dp b.cls b.wb ∧ BlocksG G l

/-- All blocks of all weights satisfy the condition of the relation. -/
def WeightsG (G : ℕ → ℕ → ℕ → ℕ → Prop) : List Weight → Prop
  | [] => True
  | w :: l => BlocksG G w.blocks ∧ WeightsG G l

theorem sqBlocks_rel : ∀ (l : List WBlk), BlocksG G l → R (sqBlocks A l) (sqBlocks B l)
  | [], _ => h.nat 0
  | _ :: l, hg => h.add (h.sq _ _ _ _ _ _ hg.1) (sqBlocks_rel l hg.2)

omit h in
theorem sosGo_cons (o : Ops α) (w : Weight) (l : List Weight) (locs : List α) (acc : α) :
    sosGo o (w :: l) locs acc
      = sosGo o l (tlA locs) (o.add acc (o.smul (Nat.shiftLeft 1 w.a) (o.mul (hdA o locs) (sqBlocks o w.blocks)))) := rfl

theorem sosGo_rel : ∀ (ws : List Weight), WeightsG G ws → ∀ {locs : List α} {locs' : List β} {acc : α} {acc' : β},
    List.Forall₂ R locs locs' → R acc acc' → R (sosGo A ws locs acc) (sosGo B ws locs' acc')
  | [], _, _, _, _, _, _, ha => ha
  | w :: l, hg, _, _, _, _, hl, ha => by
    rw [sosGo_cons, sosGo_cons]
    exact sosGo_rel l hg.2 (tlA_rel hl) (h.add ha (h.smul _ (h.mul (hdA_rel h hl) (sqBlocks_rel h _ hg.1))))

/-! ### The value of a record -/

theorem recLhs_rel (P : Par) (hd : RecH) (x : RecX) (i2p i2q mT : ℕ) {T H Wt : α} {T' H' Wt' : β} (hT : R T T')
    (hH : R H H') (hW : R Wt Wt') : R (recLhs A P hd x i2p i2q mT T H Wt) (recLhs B P hd x i2p i2q mT T' H' Wt') :=
  h.sub (h.add (h.smul _ (recHm_rel h P hd hT mT)) (h.nat _))
    (h.add (h.add (h.nat _) (kernGo_rel h _ _ _ _ _ _ _ _ _ _ (qList_rel h hH hW _ _) (h.nat 0)))
      (h.smul _ (h.add (dotS_rel h _ _ _ _ _ _ _ _) (dotS_rel h _ _ _ _ _ _ _ _))))

theorem recValK_rel (P : Par) (hd : RecH) (x : RecX) (hg : WeightsG G x.ws) (i2p i2q m1 m2 mT : ℕ)
    {U1 V1 U2 V2 T R1 R2 : α} {U1' V1' U2' V2' T' R1' R2' : β} (hU1 : R U1 U1') (hV1 : R V1 V1') (hU2 : R U2 U2')
    (hV2 : R V2 V2') (hT : R T T') (hR1 : R R1 R1') (hR2 : R R2 R2') :
    R (recValK A P hd x i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2) (recValK B P hd x i2p i2q m1 m2 mT U1' V1' U2' V2' T' R1' R2') := by
  unfold recValK
  have hH := recHv_rel h m1 m2 mT hU1 hV1 hU2 hV2 hT
  have hW := h.mul hR1 hR2
  have hs := sosGo_rel h x.ws hg (recLocs_rel h P hd i2p i2q m1 m2 mT hU1 hV1 hU2 hV2 hT hR1 hR2 hH hW) (h.nat 0)
  exact h.sub (recLhs_rel h P hd x i2p i2q mT hT hH hW)
    (cond_rel (h.add hs (h.smul _ (h.mul (h.sub hR2 hR1) (dot5_rel h _ _ _ _)))) hs)

theorem recValU_rel (P : Par) (hd : RecH) (x : RecX) (hg : WeightsG G x.ws) (i2p i2q m1 m2 : ℕ)
    {U1 V1 U2 V2 : α} {U1' V1' U2' V2' : β} (hU1 : R U1 U1') (hV1 : R V1 V1') (hU2 : R U2 U2') (hV2 : R V2 V2') :
    R (recValU A P hd x i2p i2q m1 m2 U1 V1 U2 V2) (recValU B P hd x i2p i2q m1 m2 U1' V1' U2' V2') :=
  recValK_rel h P hd x hg i2p i2q m1 m2 _ hU1 hV1 hU2 hV2 (recT_rel h P hd hU1 hV1 hU2 hV2) (clsR_rel h m1 hU1 hV1)
    (clsR_rel h m2 hU2 hV2)

/-- **The values of a record are related.** -/
theorem recVal_rel (P : Par) (hd : RecH) (x : RecX) (hg : WeightsG G x.ws) : R (recVal A P hd x) (recVal B P hd x) :=
  recValU_rel h P hd x hg _ _ _ _ (clsU_rel h _ _ _ _ _) (clsV_rel h _ _ _ _ _) (clsU_rel h _ _ _ _ _) (clsV_rel h _ _ _ _ _)

/-! ### The identity of a minorant -/

theorem minoT_rel (hd : RecH) : R (minoT A hd) (minoT B hd) :=
  cond_rel (h.add (h.smul _ (var_rel h 0)) (var_rel h 1))
    (cond_rel (h.sub (h.add (h.nat _) (h.smul _ (var_rel h 0))) (h.nat _))
      (h.sub (h.add (h.nat _) (h.smul _ (var_rel h 0))) (h.nat _)))

theorem minoLocs_rel (P : Par) (hd : RecH) {T : α} {T' : β} (hT : R T T') (mM : ℕ) :
    List.Forall₂ R (minoLocs A P hd T mM) (minoLocs B P hd T' mM) :=
  cond_rel
    (List.Forall₂.cons (h.nat 1) (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (sqr_rel h (var_rel h 0))))
      (List.Forall₂.cons (h.sub (h.nat _) (h.smul _ (sqr_rel h (var_rel h 1))))
        (List.Forall₂.cons (locT_rel h hd hT mM) List.Forall₂.nil))))
    (List.Forall₂.cons (h.sub (h.add (h.smul _ hT) (h.nat _)) (h.nat _))
      (List.Forall₂.cons (h.sub (h.nat _) (h.add (h.smul _ hT) (h.nat _))) List.Forall₂.nil))

/-- **The values of a minorant are related.** -/
theorem minoVal_rel (P : Par) (hd : RecH) (x : MinoX) (hg : WeightsG G x.ws) : R (minoVal A P hd x) (minoVal B P hd x) :=
  h.sub (h.sub (h.nat _) (h.smul _ (h.mul (h.sub (h.nat _) (minoT_rel h hd)) (dotS_rel h _ _ _ _ _ _ _ _))))
    (sosGo_rel h x.ws hg (minoLocs_rel h P hd (minoT_rel h hd) _) (h.nat 0))

/-! ### Exact parts of the weights -/

/-- All atoms of a list satisfy the condition of the relation. -/
def AtomsG (G : ℕ → ℕ → ℕ → ℕ → Prop) : List Atom → Prop
  | [] => True
  | t :: l => G t.delta t.dp t.cls t.wb ∧ AtomsG G l

/-- All atoms of all exact parts satisfy the condition of the relation. -/
def ExG (G : ℕ → ℕ → ℕ → ℕ → Prop) : List ExW → Prop
  | [] => True
  | w :: l => AtomsG G w.ats ∧ ExG G l

omit h in
theorem exG_hd : ∀ {ex : List ExW}, ExG G ex → AtomsG G (hdX ex).ats
  | [], _ => trivial
  | _ :: _, hg => hg.1

omit h in
theorem exG_tl : ∀ {ex : List ExW}, ExG G ex → ExG G (tlX ex)
  | [], _ => trivial
  | _ :: _, hg => hg.2

theorem atomVal_rel (t : Atom) (hg : G t.delta t.dp t.cls t.wb) : R (atomVal A t) (atomVal B t) :=
  h.mul (h.dg _ _ _ _ _ hg) (sqr_rel h (dot5_rel h _ _ _ _))

theorem sqAtoms_rel : ∀ (l : List Atom), AtomsG G l → R (sqAtoms A l) (sqAtoms B l)
  | [], _ => h.nat 0
  | t :: l, hg => h.add (atomVal_rel h t hg.1) (sqAtoms_rel l hg.2)

omit h in
theorem sosGoX_cons (o : Ops α) (w : Weight) (l : List Weight) (ex : List ExW) (locs : List α) (acc : α) :
    sosGoX o (w :: l) ex locs acc
      = sosGoX o l (tlX ex) (tlA locs)
        (o.add acc (o.mul (hdA o locs)
          (o.add (o.smul (Nat.shiftLeft 1 w.a) (sqBlocks o w.blocks))
            (o.smul (Nat.shiftLeft 1 (hdX ex).b) (sqAtoms o (hdX ex).ats))))) := rfl

theorem sosGoX_rel : ∀ (ws : List Weight), WeightsG G ws → ∀ {ex : List ExW}, ExG G ex →
    ∀ {locs : List α} {locs' : List β} {acc : α} {acc' : β},
    List.Forall₂ R locs locs' → R acc acc' → R (sosGoX A ws ex locs acc) (sosGoX B ws ex locs' acc')
  | [], _, _, _, _, _, _, _, _, ha => ha
  | w :: l, hg, _, he, _, _, _, _, hl, ha => by
    rw [sosGoX_cons, sosGoX_cons]
    exact sosGoX_rel l hg.2 (exG_tl he) (tlA_rel hl)
      (h.add ha (h.mul (hdA_rel h hl)
        (h.add (h.smul _ (sqBlocks_rel h _ hg.1)) (h.smul _ (sqAtoms_rel h _ (exG_hd he))))))

theorem recValKX_rel (P : Par) (hd : RecH) (x : RecX) (ex : List ExW) (hg : WeightsG G x.ws) (he : ExG G ex)
    (i2p i2q m1 m2 mT : ℕ) {U1 V1 U2 V2 T R1 R2 : α} {U1' V1' U2' V2' T' R1' R2' : β} (hU1 : R U1 U1') (hV1 : R V1 V1')
    (hU2 : R U2 U2') (hV2 : R V2 V2') (hT : R T T') (hR1 : R R1 R1') (hR2 : R R2 R2') :
    R (recValKX A P hd x ex i2p i2q m1 m2 mT U1 V1 U2 V2 T R1 R2)
      (recValKX B P hd x ex i2p i2q m1 m2 mT U1' V1' U2' V2' T' R1' R2') := by
  unfold recValKX
  have hH := recHv_rel h m1 m2 mT hU1 hV1 hU2 hV2 hT
  have hW := h.mul hR1 hR2
  have hs := sosGoX_rel h x.ws hg he (recLocs_rel h P hd i2p i2q m1 m2 mT hU1 hV1 hU2 hV2 hT hR1 hR2 hH hW) (h.nat 0)
  exact h.sub (recLhs_rel h P hd x i2p i2q mT hT hH hW)
    (cond_rel (h.add hs (h.smul _ (h.mul (h.sub hR2 hR1) (dot5_rel h _ _ _ _)))) hs)

theorem recValUX_rel (P : Par) (hd : RecH) (x : RecX) (ex : List ExW) (hg : WeightsG G x.ws) (he : ExG G ex)
    (i2p i2q m1 m2 : ℕ) {U1 V1 U2 V2 : α} {U1' V1' U2' V2' : β} (hU1 : R U1 U1') (hV1 : R V1 V1') (hU2 : R U2 U2')
    (hV2 : R V2 V2') :
    R (recValUX A P hd x ex i2p i2q m1 m2 U1 V1 U2 V2) (recValUX B P hd x ex i2p i2q m1 m2 U1' V1' U2' V2') :=
  recValKX_rel h P hd x ex hg he i2p i2q m1 m2 _ hU1 hV1 hU2 hV2 (recT_rel h P hd hU1 hV1 hU2 hV2) (clsR_rel h m1 hU1 hV1)
    (clsR_rel h m2 hU2 hV2)

/-- **The values of a record with exact parts are related.** -/
theorem recValX_rel (P : Par) (hd : RecH) (x : RecX) (ex : List ExW) (hg : WeightsG G x.ws) (he : ExG G ex) :
    R (recValX A P hd x ex) (recValX B P hd x ex) :=
  recValUX_rel h P hd x ex hg he _ _ _ _ (clsU_rel h _ _ _ _ _) (clsV_rel h _ _ _ _ _) (clsU_rel h _ _ _ _ _)
    (clsV_rel h _ _ _ _ _)

/-- **The values of a minorant with exact parts are related.** -/
theorem minoValX_rel (P : Par) (hd : RecH) (x : MinoX) (ex : List ExW) (den : ℕ) (hg : WeightsG G x.ws) (he : ExG G ex) :
    R (minoValX A P hd x ex den) (minoValX B P hd x ex den) :=
  h.sub (h.sub (h.nat _) (h.smul _ (h.mul (h.sub (h.nat _) (minoT_rel h hd)) (dotS_rel h _ _ _ _ _ _ _ _))))
    (sosGoX_rel h x.ws hg he (minoLocs_rel h P hd (minoT_rel h hd) _) (h.nat 0))

/-! ### The identity of a label -/

theorem piTerm_rel (P : Par) (heads : List RecH) (l ot : ℕ) : R (piTerm A P heads l ot) (piTerm B P heads l ot) :=
  cond_rel (dotS_rel h _ _ _ _ _ _ _ _) (dotS_rel h _ _ _ _ _ _ _ _)

omit h in
theorem clsPhiGo_succ (o : Ops α) (P : Par) (heads : List RecH) (l n : ℕ) (acc : α) :
    clsPhiGo o P heads l (n + 1) acc = clsPhiGo o P heads l n (cond (Nat.beq n l) acc (o.add acc (piTerm o P heads l n))) := rfl

theorem clsPhiGo_rel (P : Par) (heads : List RecH) (l : ℕ) :
    ∀ (n : ℕ) {acc : α} {acc' : β}, R acc acc' → R (clsPhiGo A P heads l n acc) (clsPhiGo B P heads l n acc')
  | 0, _, _, ha => ha
  | n + 1, _, _, ha => by
    rw [clsPhiGo_succ, clsPhiGo_succ]
    exact clsPhiGo_rel P heads l n (cond_rel ha (h.add ha (piTerm_rel h P heads l n)))

omit h in
theorem clsDeltaGo_cons (o : Ops α) (cls sg : ℕ) (Rv : α) (blks : List Blk) (l : List (List Blk)) (aK : List ℕ) (Rk acc : α) :
    clsDeltaGo o cls sg Rv (blks :: l) aK Rk acc
      = clsDeltaGo o cls sg Rv l (tl aK) (o.mul Rk Rv)
        (cond (usedK cls cls blks)
          (o.add acc (o.smul (Nat.shiftLeft 1 (hd aK)) (o.mul Rk (innerK o cls sg 0 1 cls sg 0 1 blks (o.nat 0)))))
          acc) := rfl

theorem clsDeltaGo_rel (cls sg : ℕ) {Rv : α} {Rv' : β} (hR : R Rv Rv') :
    ∀ (l : List (List Blk)) (aK : List ℕ) {Rk acc : α} {Rk' acc' : β}, R Rk Rk' → R acc acc' →
      R (clsDeltaGo A cls sg Rv l aK Rk acc) (clsDeltaGo B cls sg Rv' l aK Rk' acc')
  | [], _, _, _, _, _, _, ha => ha
  | blks :: l, aK, _, _, _, _, hk, ha => by
    rw [clsDeltaGo_cons, clsDeltaGo_cons]
    exact clsDeltaGo_rel cls sg hR l _ (h.mul hk hR)
      (cond_rel (h.add ha (h.smul _ (h.mul hk (innerK_rel h _ _ _ _ _ _ _ _ _ (h.nat 0))))) ha)

theorem clsLam_rel (P : Par) (cls : ℕ) : R (clsLam A P cls) (clsLam B P cls) := by
  unfold clsLam
  have hh := h.add (sqr_rel h (var_rel h 0)) (sqr_rel h (var_rel h 1))
  exact cond_rel (h.nat 0) (h.add (h.smul _ (h.mul (sqr_rel h hh) (h.sub (h.nat _) (h.smul _ hh)))) (h.smul _ hh))

/-- **The values of the identity of a label are related.** -/
theorem clsVal_rel (P : Par) (heads : List RecH) (x : ClsX) : R (clsVal A P heads x) (clsVal B P heads x) :=
  h.sub (h.smul _ (clsPhiGo_rel h P heads x.label 9 (h.nat 0)))
    (h.add
      (clsDeltaGo_rel h _ _ (clsR_rel h _ (clsU_rel h _ _ _ _ _) (clsV_rel h _ _ _ _ _)) _ _ (h.nat 1) (h.nat 0))
      (h.smul _ (clsLam_rel h P _)))

end

end CAP.VR
