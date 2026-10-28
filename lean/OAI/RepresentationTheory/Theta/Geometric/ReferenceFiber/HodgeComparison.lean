import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.MarkingKernel
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedKernel
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedPolarization
import OAI.RepresentationTheory.Theta.Geometric.Universal.DistinguishedRank

/-! # Hodge Comparison -/

namespace OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.HodgeComparison

noncomputable section

/-! Local reference coordinates determine a full Hodge comparison
from their actual reference moduli fiber to the nearby universal fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

local instance : IsReduced (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)).left :=
  inferInstanceAs (IsReduced (Spec (.of ℂ)))

namespace ActiveHeckeThetaData.ReferencePELPointData

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    {D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA}
    {hg : D.pel.HasIntegralModelGeometry} {a : D.domain} (R : D.ReferencePELPointData hg a)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsReduced S.left] (f : S ⟶ D.pel.complexSpace)
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (Universal.PELConditions.complexUniversalPolarized D.pel hg f).abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
      (Universal.PELConditions.complexUniversalAction D.pel hg f) F)
    (z₀ : H.compatible.neighborhood) (hz₀ : Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = R.point)

variable {b : D.domain} (R' : D.ReferencePELPointData hg b)
    (z : H.compatible.neighborhood)

def _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety ≃ₗ[ℚ]
        AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
          (Intrinsic.FamilyFrames.familyChartParameter C z)).variety :=
  FieldMarkingCoordinateChange.fieldMarkingPeriodComparison (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
    (Universal.PELConditions.complexUniversalAction D.pel hg R'.point) (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
    (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
    (Intrinsic.FamilyFrames.familyChartParameter C z)
    (R'.nativeUniversalFieldMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (R.transportedFieldMarking f H z₀ hz₀ z)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData.ReferencePELPointData.referenceFiberComparison_isHodgeMap (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val}) :
    AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure
      (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point)
        (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))).variety)
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (PolarizedCanonicalForm.polarizedFamilyPresentation (Universal.PELConditions.complexUniversalPolarized D.pel hg f)
        (Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (R.referenceFiberComparison f H z₀ hz₀ R' z).toLinearMap := by
  apply FieldMarkingHodgeComparison.fieldMarkingPeriodComparison_isHodgeMap
    (Universal.PELConditions.complexUniversalPolarized D.pel hg R'.point) (Universal.PELConditions.complexUniversalAction D.pel hg R'.point)
    (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
    (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
    (Intrinsic.FamilyFrames.familyChartParameter C z) s hs rfl hdegree
    (R'.nativeUniversalFieldMarking R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (R.transportedFieldMarking f H z₀ hz₀ z) D.pel.reference hg.reference_admissible
    ((Universal.PELConditions.complexUniversal_rosati D.pel hg R'.point).pullback _ _ (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))
    ((Universal.PELConditions.complexUniversal_rosati D.pel hg f).pullback _ _ (Intrinsic.FamilyFrames.familyChartParameter C z).left)
  · intro v w
    exact (R.transportedFieldMarking_polarization f H z₀ hz₀ z v w).trans
      (R'.nativeUniversalRationalMarking_polarization R'.point
        (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v w).symm
  · exact (R'.nativeUniversalFieldMarking_kernel R'.point
      (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _)).trans
      (hk.symm.trans (R.transportedReferenceMatrix_kernel f H z₀ hz₀ z))
  · exact Universal.DistinguishedRank.complexUniversal_embedding_rank D.pel hg R'.point (𝟙 (Over.mk (𝟙 AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase)))
  · exact Universal.DistinguishedRank.complexUniversal_embedding_rank D.pel hg f (Intrinsic.FamilyFrames.familyChartParameter C z)

end ActiveHeckeThetaData.ReferencePELPointData

end

end OAI.RepresentationTheory.Theta.Geometric.ReferenceFiber.HodgeComparison
