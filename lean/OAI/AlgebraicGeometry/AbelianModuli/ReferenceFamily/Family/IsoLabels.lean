import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Family.Matrices
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison
import OAI.RepresentationTheory.Theta.Geometric.BaseChangeCancellation

/-! # Iso Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Every actual isomorphism from a reference fiber to a chart fiber
produces a rational label whose holomorphic matrix has the exact reference
ball line as its kernel at that parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation Family.MarkingCoordinates.markingComplexBasis
  Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceMarkedMatrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A ρ F)
    {s : ℕ} {P : Datum.RankThreePELDatum E s} {hP : P.IsAdmissible}
    {y : P.domain} {R : Reference.Fiber.ReferenceAnalyticFiber P y} (M : Reference.AlgebraicModel.ReferenceAlgebraicModel R hP)
    (z : H.compatible.neighborhood)
    (e : M.abelian.toOver ≅ (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation A (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
    [IsMonHom e.hom]

def Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceIsoLabel : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C) :=
  (H.rationalTransport z).symm.toLinearMap.comp
    ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp M.nativeReferenceMarking.toLinearMap)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceIsoLabel_complex (u : ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((H.referenceIsoLabel M z e).baseChange ℂ u) =
      (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ (M.nativeComplexReferenceMarking u) := by
  exact (RepresentationTheory.Theta.Geometric.BaseChangeCancellation.baseChange_equiv_cancel (H.rationalTransport z)
    ((Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp M.nativeReferenceMarking.toLinearMap) u).trans
      (LinearMap.congr_fun (LinearMap.baseChange_comp M.nativeReferenceMarking.toLinearMap
        (Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom)) u)

theorem Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport.referenceIsoLabel_kernel :
    (H.referenceMarkedMatrix P hP (H.referenceIsoLabel M z e) z).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector y.val} := by
  apply Submodule.ext
  intro v
  change H.referenceMarkedMatrix P hP (H.referenceIsoLabel M z e) z v = 0 ↔ _
  rw [H.referenceMarkedMatrix_kernel_iff, H.referenceIsoLabel_complex]
  exact (RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff e (M.nativeComplexReferenceMarking
    (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v))).trans (RepresentationTheory.Theta.Geometric.Reference.FirstEmbedding.nativeReferenceFirst_kernel P hP M v)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
