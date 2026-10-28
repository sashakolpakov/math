import OAI.RepresentationTheory.Theta.Geometric.Reference.GenericPELFamily
import OAI.RepresentationTheory.Theta.Geometric.Reference.PELFrameLattices
import OAI.RepresentationTheory.Theta.Geometric.PELFrameTransport
import OAI.RepresentationTheory.Theta.Geometric.Complex.TateBase
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IsogenyQuotientConstructedPosition

/-! # Generic Frame Data -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! The actual original generic reference fiber has a constructed split
Tate frame with exactly the standard chosen and opposite source lattices. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (R : D.ReferencePELPointData hg x)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.genericFamilyIso Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame
  AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberFamily Data.ActiveHeckeThetaData.ReferencePELPointData.family Data.ActiveHeckeThetaData.ReferencePELPointData.genericPoint AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame

def Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame :=
  AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame (R := NumberField.RingOfIntegers E) (g := 3 * s)
    (N := D.pel.level) (s := s) (q := q) (S := Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField)))
    (F := D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint)
    (G := R.family) (Over.mk (𝟙 (Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))))) R.genericFamilyIso (Geometric.Complex.TateBase.complexTateFrame_base (R.pelTateFrame hgood hdegree))

end

/-! The actual original generic reference fiber has a constructed split
Tate frame with exactly the standard chosen and opposite source lattices. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj TensorProduct

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {x : D.domain}
    (R : D.ReferencePELPointData hg x)
    (hgood : D.pel.IsGoodCompletelySplitPrime) (hdegree : Module.finrank ℚ E = 2 * s)

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.genericFamilyIso Data.ActiveHeckeThetaData.PeriodModel.referenceTateFrame Data.ActiveHeckeThetaData.ReferencePELPointData.pelTateFrame
  AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData.fiberFamily Data.ActiveHeckeThetaData.ReferencePELPointData.family Data.ActiveHeckeThetaData.ReferencePELPointData.genericPoint AlgebraicGeometry.AbelianScheme.TateComparison.PELModuli.PELFamilyIso.transportFrame

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame_isSplitAction (hc : D.HasFiniteCoordinates) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.IsSplitActionFrame (S := Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField)))
      (D.pel.fiberFamily (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint)
      (Over.mk (𝟙 (Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))))) q D.pel.localCharacter (R.genericTateFrame hgood hdegree) := by
  rw [Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame]
  exact R.genericFamilyIso.transportFrame_equivariant (Over.mk (𝟙 (Spec (@CommRingCat.of ℂ (@Field.toCommRing ℂ Complex.instField))))) D.pel.localCharacter
    (Geometric.Complex.TateBase.complexTateFrame_base (R.pelTateFrame hgood hdegree))
    (Geometric.Complex.TateBase.complexTateFrame_base_equivariant D.pel.localCharacter (R.pelTateFrame hgood hdegree)
      (R.pelTateFrame_isSplitAction hgood hdegree hc))

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame_integral_image (hc : D.HasFiniteCoordinates) :
    AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (R.genericTateFrame hgood hdegree) = D.jointLocalLattice := by
  rw [Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame, PELFrameTransport.pelFrameTransport_integral, Geometric.Complex.TateBase.complexTateFrame_base_integral]
  exact R.pelTateFrame_integral_image hgood hdegree hc

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.genericTateFrame_sourceLattice (hc : D.HasFiniteCoordinates) (v : Fin s × Bool) :
    D.pel.framedFiberSourceLattice (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ≫ D.pel.complexGenericPoint) R.genericPoint
      (R.genericTateFrame hgood hdegree) v = AlgebraicGeometry.AbelianScheme.TateComparison.RelativePositionChoices.standardRankThreeLattice q := by
  apply Subtype.ext
  change (AlgebraicGeometry.AbelianScheme.TateComparison.Rational.framedIntegralTateImage (R.genericTateFrame hgood hdegree)).map
    ((LinearMap.proj v : AlgebraicGeometry.AbelianScheme.TateComparison.Rational.SplitTateSpace s q →ₗ[ℚ_[q]] (Fin 3 → ℚ_[q])).restrictScalars ℤ_[q]) = _
  rw [R.genericTateFrame_integral_image hgood hdegree hc,
    Data.ActiveHeckeThetaData.jointLocalLattice_eq_pi_standard (hg := hg) hgood hc]
  change (Submodule.pi Set.univ (fun _ : Fin s × Bool => Data.ActiveHeckeThetaData.standardLocalLattice (q := q))).map
    (LinearMap.proj v) = AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockHeckeChoices.Construction.standardBlockLattice q
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.FramedSourceDecomposition.submodule_pi_map_proj]
  exact Cleared.LocalInverseLattice.standardLocalLattice_eq_standardBlockLattice q

end

end OAI.RepresentationTheory.Theta.Geometric
