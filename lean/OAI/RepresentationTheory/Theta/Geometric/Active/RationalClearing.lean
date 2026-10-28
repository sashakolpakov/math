import OAI.RepresentationTheory.Theta.Geometric.ExactClearingLattice
import OAI.RepresentationTheory.Theta.Geometric.Cleared.ReferencePELIsogeny
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.Trace

/-! # Rational Clearing -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every individual active coset has a rational SU representative with
the original full away marking and the exact prescribed clearing. -/

set_option backward.isDefEq.respectTransparency false

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [IsTopologicalGroup Ga]
    [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.active_coset_rational_representative (hArithmetic : DenseRange D.rationalFinite)
    (a : Intrinsic.Hecke.ActiveWeight) (c : Intrinsic.Hecke.activeCosets q a) :
    ∃ g : D.RationalSU,
      (QuotientGroup.mk (D.activeLocal g)⁻¹ : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = c.val ∧
      D.away g ∈ D.awayLevel ∧
      DoubleCosets.Spherical.InDoubleCoset (SphericalGU.Spherical.integralSL3 q) (Intrinsic.Hecke.activeSLRepresentative q a)⁻¹
        (D.activeLocal g)⁻¹ := by
  let g := BranchTrace.activeRationalRepresentative D.rationalFinite hArithmetic D.integralOpen D.awayLevel c.val
  have hm := BranchTrace.activeRationalRepresentative_mem D.rationalFinite hArithmetic D.integralOpen D.awayLevel c.val
  have hq : D.activeLocal g * c.val.out ∈ SphericalGU.Spherical.integralSL3 q := hm.1
  have ha : D.away g ∈ D.awayLevel := by
    have h := hm.2
    change D.away g * 1 ∈ D.awayLevel at h
    simpa only [mul_one] using h
  have he : (QuotientGroup.mk (D.activeLocal g)⁻¹ :
      SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = c.val := by
    calc
      _ = QuotientGroup.mk c.val.out := QuotientGroup.eq.mpr (by simpa only [inv_inv] using hq)
      _ = c.val := Quotient.out_eq c.val
  refine ⟨g, he, ha, ?_⟩
  obtain ⟨h, hh, hc⟩ := c.property
  exact Cleared.LocalMatrices.inDoubleCoset_of_quotient_eq (SphericalGU.Spherical.integralSL3 q) (he.trans hh.symm) hc

theorem Data.ActiveHeckeThetaData.active_coset_exact_rational_clearing (hg : D.pel.HasIntegralModelGeometry)
    (hc : D.HasFiniteCoordinates) (hgood : D.pel.IsGoodCompletelySplitPrime)
    (hdegree : Module.finrank ℚ E = 2 * s) (hArithmetic : DenseRange D.rationalFinite)
    (a : Intrinsic.Hecke.ActiveWeight) (c : Intrinsic.Hecke.activeCosets q a) :
    ∃ g : D.RationalSU,
      (QuotientGroup.mk (D.activeLocal g)⁻¹ : SphericalGU.Spherical.SL3 q ⧸ SphericalGU.Spherical.integralSL3 q) = c.val ∧
      D.away g ∈ D.awayLevel ∧
      ∀ u ∈ D.pel.reference.lattice,
        (q : ℤ) ^ Intrinsic.Hecke.clearingExponent D.pel.reference.distinguished a • D.rationalLinear g u ∈
          D.pel.reference.lattice := by
  obtain ⟨g, he, ha, hcos⟩ := D.active_coset_rational_representative hArithmetic a c
  exact ⟨g, he, ha, D.active_doubleCoset_exact_clearing hg hc hgood hdegree a g ha hcos⟩

end

end OAI.RepresentationTheory.Theta.Geometric
