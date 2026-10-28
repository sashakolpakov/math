import OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall
import OAI.RepresentationTheory.Theta.Geometric.ReferenceUniversal.ImaginarySign
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedKernel
import OAI.RepresentationTheory.Theta.Geometric.Reference.TransportedPolarization

/-! # Transported Ball -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every fiber of the common compatible neighborhood has a literal
reference ball kernel under the same original transported field marking. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] Data.ActiveHeckeThetaData.ReferencePELPointData.nativeUniversalFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
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

theorem Data.ActiveHeckeThetaData.ReferencePELPointData.transportedReferenceKernel_ball (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (z : H.compatible.neighborhood) :
    ∃ b : D.domain, (H.referenceMarkedMatrix D.pel.reference hg.reference_admissible
      (R.transportedReferenceLabel f H z₀ hz₀) z).ker = Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val} := by
  obtain ⟨w, hw⟩ := Reference.FieldMarkingBall.fieldMarking_referenceBallCoordinate
    (Universal.PELConditions.complexUniversalPolarized D.pel hg f) (Universal.PELConditions.complexUniversalAction D.pel hg f)
    (Intrinsic.FamilyFrames.familyChartParameter C z) s hs rfl hdegree (R.transportedFieldMarking f H z₀ hz₀ z)
    (Universal.PELConditions.complexUniversal_rosati D.pel hg f) D.pel.reference hg.reference_admissible
    (R.transportedFieldMarking_polarization f H z₀ hz₀ z)
    (R.nativeUniversal_referenceImaginary_positive f (Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ hs hdegree)
    (Universal.DistinguishedRank.complexUniversal_distinguished_rank D.pel hg f (Intrinsic.FamilyFrames.familyChartParameter C z))
  refine ⟨⟨w.val, ?_⟩, (R.transportedReferenceMatrix_kernel f H z₀ hz₀ z).trans hw⟩
  change w.val ∈ (D.domain : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
  rw [← D.reference_domain_eq]
  exact w.property

end

end OAI.RepresentationTheory.Theta.Geometric
