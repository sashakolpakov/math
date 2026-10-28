import OAI.RepresentationTheory.Theta.Geometric.Reference.GenericFrameData
import OAI.RepresentationTheory.Theta.Geometric.Cleared.GenericIsogeny
import OAI.RepresentationTheory.Theta.Geometric.Complex.TateBase

/-! # PEL Type -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Actual original cleared PEL isogenies have the exact inverse local
lattices, including after transport to the universal geometric fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x y : D.domain}
    (R : D.ReferencePELPointData hg x) (S : D.ReferencePELPointData hg y)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)
    (hc : D.HasFiniteCoordinates) (g : D.RationalSU) (n : ℕ)
    (e : AlgebraicGeometry.AbelianScheme.TateComparison.PELIsogenies.PELIsogeny R.family
      (S.family.shiftMarking (ZMod.unitOfCoprime (q ^ n) (hgood.2.2.1.pow_left n))) (q ^ (2 * n)))
    (ht : ∀ u, AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.isogeny.hom
      ((R.model.toNativeReferenceModel R.analytic).nativeReferenceMarking u) =
      (S.model.toNativeReferenceModel S.analytic).nativeReferenceMarking
        ((q : ℤ) ^ n • D.rationalLinear g u))

attribute [local irreducible] Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame

include hc ht in
theorem Data.ActiveHeckeThetaData.clearedPEL_framedLattice (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (R.pelTateFrame hgood hdegree) e.isogeny.hom v =
      (Data.ActiveHeckeThetaData.clearedLocalInverseLattice g n v).val := by
  have H := Data.ActiveHeckeThetaData.cleared_reference_framed_lattice R.model R.analytic S.model S.analytic
    hgood hdegree hc e.isogeny.hom n g ht v
  rw [Data.ActiveHeckeThetaData.clearedLocalInverseLattice_val, Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame]
  exact H

include hc ht in
theorem Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny_lattice
    (hIsogenyQuotient : D.pel.RealizesIsogenyQuotient) (A : TateComparison.Action D.pel)
    (hA : A.IsRealization D.pel hg hgood hIsogenyQuotient) (v : Fin s × Bool) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedTateLattice (R.genericTateFrame hgood hdegree)
      (Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny R S hgood hIsogenyQuotient A hA n e).isogeny.hom v =
        (Data.ActiveHeckeThetaData.clearedLocalInverseLattice g n v).val := by
  rw [Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame, Data.ActiveHeckeThetaData.clearedReferenceGenericIsogeny,
    PELFrameTransport.pelIsogeny_transport_framed_lattice, Complex.TateBase.complexTateFrame_base_lattice]
  exact Data.ActiveHeckeThetaData.clearedPEL_framedLattice R S hgood hdegree hc g n e ht v

end

end OAI.RepresentationTheory.Theta.Geometric
