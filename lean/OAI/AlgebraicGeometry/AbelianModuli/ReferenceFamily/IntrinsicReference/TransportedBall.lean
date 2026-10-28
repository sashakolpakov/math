import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestMarkingKernel
import OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall

/-! # Transported Ball -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The original reference polarization fixes the distinguished sign.
Consequently every transported kernel in the actual family neighborhood
is a line belonging to the literal original reference ball. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)

theorem Models.FinePELModel.nativeReferenceTest_imaginary_positive
    (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hy : y ≫ f = M.referencePoint hM κ hP hκ a)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    0 < ((P.embeddings P.distinguished) (RepresentationTheory.Theta.Geometric.Reference.DiagonalHermitian.referenceTraceScalar P)).im := by
  apply RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall.fieldMarking_referenceImaginary_positive (M.complexTestFamily κ f).polarized
    (M.complexTestFamily κ f).action y s hs rfl hdegree
    (M.nativeReferenceTestFieldMarking hM κ hP hκ f a y hy)
    (M.complexTestFamily κ f).rosati P hP
    (fun v w => M.nativeReferenceTestRationalMarking_polarization hM κ hP hκ f a y hy v w) a
  exact M.nativeReferenceTestFieldMarking_kernel hM κ hP hκ f a y hy

variable [IsGalois ℚ E]
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)

theorem Models.FinePELModel.transportedNativeReferenceKernel_ball
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (z : H.compatible.neighborhood) :
    ∃ b : P.domain,
      (H.referenceMarkedMatrix P hP
        (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
          Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val} := by
  let A := M.complexTestFamily κ f
  have hr := A.complexFiber_distinguished_rank κ hκ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left
    (Complex.BallPeriods.restrictComplexBase_point κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) hP
  obtain ⟨b, hb⟩ := RepresentationTheory.Theta.Geometric.Reference.FieldMarkingBall.fieldMarking_referenceBallCoordinate A.polarized A.action
    (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s hs rfl hdegree
    (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z) A.rosati P hP
    (M.transportedNativeReferenceFieldMarking_polarization hM κ hP hκ f a H z₀ hz₀ z)
    (M.nativeReferenceTest_imaginary_positive hM κ hP hκ f a (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀) hz₀ hs hdegree) hr
  exact ⟨b, (M.transportedNativeReferenceMatrix_kernel hM κ hP hκ f a H z₀ hz₀ z).trans hb⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
