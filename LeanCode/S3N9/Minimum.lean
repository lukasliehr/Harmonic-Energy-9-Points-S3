module

public import S3N9.Core

/-!
# The theorem for nine points: the lower bound

`lower_and_contacts`: for nine distinct points of the unit sphere of `ℝ⁴`, given by their coordinates, the energy
is at least `35 / 2`; if it is at most `35 / 2`, a relabelling of the points lies in the inner piece and has the
contacts. `minimum9_of`: the first part of the theorem, `S3N9.Minimum9`.

The hypotheses are the six statements that the certificates provide, in the terms of the paper:

* `Excl claims54`, `ExclL0`: the 54 cells other than L3-k2 (typed certificates, untyped certificate);
* `Excl claimsRing`, `ExclSel claimsSel`: the leaves *main*, *aux1* and the four selected-edge leaves of L3-k2;
* `ExclLeaves leavesVR`: the eleven leaves of the core with a virtual-root certificate;
* `InnerOK`: the inner piece (sharp certificate).

The generated module `T8A` (`certgen/s3n9_cells.py`, compiled by `scaling/t8_cells.py` with the modules of the
certificates) proves the six statements and applies this theorem. The proof of the theorem follows
`prop:inequality` of the source: a configuration with energy at most `35 / 2` is separated (C1), has a chain
labelling (A3), and lies in the cell L3-k2, in the cell L0 or in a claim of one of the other cells (A4).
-/

@[expose] public section

namespace S3N9

/-- **The lower bound, with the contacts in the case of equality.** -/
theorem lower_and_contacts (h54 : Excl claims54) (hL0 : ExclL0) (hR : Excl claimsRing) (hS : ExclSel claimsSel)
    (hV : ExclLeaves leavesVR) (hI : InnerOK) {x : Fin 9 → Fin 4 → ℝ} (hx : OnSphere x)
    (hinj : Function.Injective x) :
    35 / 2 ≤ energy x
      ∧ (energy x ≤ 35 / 2 → ∃ μ : Equiv.Perm (Fin 9), InLeaf Leaf.I (pt x ∘ μ) ∧ Contacts (pt x ∘ μ)) := by
  rw [energy_eq]
  have hu := (onSphere_iff x).1 hx
  have hi := (injective_pt x).2 hinj
  by_cases hE : energyE (pt x) ≤ 35 / 2
  · have hs := separated_of_energy hu hi hE
    obtain ⟨σ, hc⟩ := exists_chain (pt x) 4 le_rfl
    have huy : ∀ i, ‖(pt x ∘ σ) i‖ = 1 := fun i => hu (σ i)
    have hsy : Separated (pt x ∘ σ) := fun i j hij => hs (σ i) (σ j) (σ.injective.ne hij)
    have ey : energyE (pt x ∘ σ) = energyE (pt x) := energyE_comp_perm (pt x) σ
    rcases cells54 huy hsy hc with ⟨h0, h1, h2⟩ | h0 | ⟨c, hc', hin⟩
    · obtain ⟨a, b⟩ := l3k2_energy hR hS hV hI huy hsy hc h0 h1 h2
      rw [ey] at a b
      refine ⟨a, fun hle => ?_⟩
      obtain ⟨ρ, b1, b2⟩ := b hle
      have e2 : (pt x ∘ ⇑σ) ∘ ⇑ρ = pt x ∘ ⇑(σ * ρ) := by
        rw [Equiv.Perm.coe_mul]
        rfl
      rw [e2] at b1 b2
      exact ⟨σ * ρ, b1, b2⟩
    · have := hL0 (pt x ∘ σ) huy hsy (fun m n hmn => le_trans h0 (mval_zero_le hc hmn))
      rw [ey] at this
      exact ⟨le_of_lt this, fun hle => absurd hle (not_le.2 this)⟩
    · have := h54 c hc' (pt x ∘ σ) hin
      rw [ey] at this
      exact ⟨le_of_lt this, fun hle => absurd hle (not_le.2 this)⟩
  · rw [not_le] at hE
    exact ⟨le_of_lt hE, fun hle => absurd hle (not_le.2 hE)⟩

/-- **The harmonic energy of nine distinct points of the three-sphere is at least `35 / 2`**, given the statements
of the certificates. -/
theorem minimum9_of (h54 : Excl claims54) (hL0 : ExclL0) (hR : Excl claimsRing) (hS : ExclSel claimsSel)
    (hV : ExclLeaves leavesVR) (hI : InnerOK) : Minimum9 :=
  fun _ hx hinj => (lower_and_contacts h54 hL0 hR hS hV hI hx hinj).1

/-- info: 'S3N9.lower_and_contacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lower_and_contacts

end S3N9
