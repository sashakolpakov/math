import OAI.RepresentationTheory.Theta.Geometric.Rational.ReferenceMatrices
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.IsoKernelComparison
import OAI.RepresentationTheory.Theta.Geometric.BaseChangeCancellation

/-! # Iso Labels -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! Every actual isomorphism from a reference fiber to a chart fiber
produces a rational label whose holomorphic matrix has the exact reference
ball line as its kernel at that parameter. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical _root_.CategoryTheory.MonObj

attribute [local irreducible] PolarizedCanonicalForm.polarizedFamilyPresentation MarkingComplexTransport.markingComplexBasis
  Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceMarkedMatrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {g N : ℕ} {δ : Fin g → ℕ}
    {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S.left}
    {ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian}
    {x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S} {C : AlgebraicGeometry.PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.abelian x}
    {F : Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}

variable (H : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport A ρ F)
    {s : ℕ} {P : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {hP : P.IsAdmissible}
    {y : P.domain} {R : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.Fiber.ReferenceAnalyticFiber P y} (M : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.AlgebraicModel.ReferenceAlgebraicModel R hP)
    (z : H.compatible.neighborhood)
    (e : M.abelian.toOver ≅ (PolarizedCanonicalForm.polarizedFamilyPresentation A (Intrinsic.FamilyFrames.familyChartParameter C z)).variety.toOver)
    [IsMonHom e.hom]

def Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceIsoLabel : Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.RationalReferenceLabel (E := E) (A := A) (C := C) :=
  (H.rationalTransport z).symm.toLinearMap.comp
    ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp M.nativeReferenceMarking.toLinearMap)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceIsoLabel_complex (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)) :
    (H.rationalTransport z).toLinearMap.baseChange ℂ
      ((H.referenceIsoLabel M z e).baseChange ℂ u) =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).baseChange ℂ (M.nativeComplexReferenceMarking u) := by
  exact (BaseChangeCancellation.baseChange_equiv_cancel (H.rationalTransport z)
    ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom).comp M.nativeReferenceMarking.toLinearMap) u).trans
      (LinearMap.congr_fun (LinearMap.baseChange_comp M.nativeReferenceMarking.toLinearMap
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralMaps.IntrinsicLinearMaps.rationalLift e.hom)) u)

theorem Intrinsic.HolomorphicTransport.NativeHolomorphicTransport.referenceIsoLabel_kernel :
    (H.referenceMarkedMatrix P hP (H.referenceIsoLabel M z e) z).ker =
      Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector y.val} := by
  apply Submodule.ext
  intro v
  change H.referenceMarkedMatrix P hP (H.referenceIsoLabel M z e) z v = 0 ↔ _
  rw [H.referenceMarkedMatrix_kernel_iff, H.referenceIsoLabel_complex]
  exact (Intrinsic.IsoKernelComparison.nativeIso_period_kernel_iff e (M.nativeComplexReferenceMarking
    (Reference.FirstEmbedding.referenceFirstComplexInclusion P hP v))).trans (Reference.FirstEmbedding.nativeReferenceFirst_kernel P hP M v)

end

end OAI.RepresentationTheory.Theta.Geometric
