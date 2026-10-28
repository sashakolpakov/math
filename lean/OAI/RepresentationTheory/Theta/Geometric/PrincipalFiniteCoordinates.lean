import OAI.RepresentationTheory.Theta.Geometric.PrincipalLocalMatrices
import OAI.RepresentationTheory.Theta.Geometric.PrincipalAwayLattice

/-! # Principal Finite Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Principal congruence on the actual reference lattice implies
membership in the precise finite subgroup used in GeometricTheta. -/

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.principal_finite_membership (hc : D.HasFiniteCoordinates) (g : D.RationalSU)
    (hg : ∀ x, x ∈ D.pel.reference.lattice ↔ D.rationalLinear g x ∈ D.pel.reference.lattice)
    (hl : ∀ x ∈ D.pel.reference.lattice, ∃ y ∈ D.pel.reference.lattice,
      D.rationalLinear g x - x = D.pel.level • y) :
    D.rationalFinite g ∈ (SphericalGU.Spherical.integralSL3 q).prod D.awayLevel.toSubgroup := by
  have hint (v) := D.localMatrix_integral_of_reference_lattice hc g (fun x hx => (hg x).mp hx) v
  exact ⟨hint (D.pel.reference.distinguished, false),
    (hc.2.2 g).mpr ⟨D.principal_mem_rationalAwayLevel g hg hl, fun v _ => hint v⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric
