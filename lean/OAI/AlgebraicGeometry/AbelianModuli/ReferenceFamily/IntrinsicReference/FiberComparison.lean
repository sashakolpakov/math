import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedForm
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TransportedKernel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.TestMarkingKernel
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison

/-! # Fiber Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The exact transported kernel determines a full native Hodge comparison
from the actual reference moduli fiber to the nearby test-family fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily Models.FinePELModel.nativeReferenceTestFiberIso
  RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.ChernPairing.nativePolarizationForm Models.FinePELModel.nativeReferenceTestRationalMarking

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    [Field K] {s N : ℕ} [NeZero N] {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (M : Models.FinePELModel P iota N) (hM : M.IsFine) (κ : K →+* ℂ)
    (hP : P.IsAdmissible) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : S ⟶ M.complexFiber κ) (a : P.domain)
    {x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S}
    {C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts (M.complexTestFamily κ f).polarized.abelian x}
    {F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C}
    (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport (M.complexTestFamily κ f).polarized
      (M.complexTestFamily κ f).action F)
    (z₀ : H.compatible.neighborhood)
    (hz₀ : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z₀ ≫ f = M.referencePoint hM κ hP hκ a)
    (b : P.domain) (z : H.compatible.neighborhood)

def Models.FinePELModel.nativeReferenceFiberComparison :
    Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety ≃ₗ[ℚ]
        Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
          (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety :=
  RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange.fieldMarkingPeriodComparison
    (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
    (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
    (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    (M.nativeReferenceTestFieldMarking hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z)

theorem Models.FinePELModel.nativeReferenceFiberComparison_marking (v : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z
      (M.nativeReferenceTestRationalMarking hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
        (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v) =
      M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z v := by
  have he := RepresentationTheory.Theta.Geometric.FieldMarkingCoordinateChange.fieldMarkingPeriodComparison_marking
    (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
    (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
    (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
    (M.nativeReferenceTestFieldMarking hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z) v
  rw [M.nativeReferenceTestFieldMarking_apply] at he
  exact he

variable [IsGalois ℚ E]

theorem Models.FinePELModel.nativeReferenceFiberComparison_isHodgeMap
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s)
    (hk : (H.referenceMarkedMatrix P hP
      (M.transportedNativeReferenceLabel hM κ hP hκ f a H z₀ hz₀) z).ker =
        Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector b.val}) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety)
      (IntrinsicPeriodHodgeStructure.IntrinsicRationalPeriods.nativePeriodHodgeStructure (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety)
      (M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z).toLinearMap := by
  let A := M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)
  let B := M.complexTestFamily κ f
  apply RepresentationTheory.Theta.Geometric.FieldMarkingHodgeComparison.fieldMarkingPeriodComparison_isHodgeMap A.polarized A.action (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))
    B.polarized B.action (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) s hs rfl hdegree
    (M.nativeReferenceTestFieldMarking hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _))
    (M.transportedNativeReferenceFieldMarking hM κ hP hκ f a H z₀ hz₀ z) P hP
    (A.rosati.pullback _ _ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)) (B.rosati.pullback _ _ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left)
  · intro v w
    rw [M.nativeReferenceTestFieldMarking_apply]
    exact (M.transportedNativeReferenceFieldMarking_polarization hM κ hP hκ f a H z₀ hz₀ z v w).trans
      (M.nativeReferenceTestRationalMarking_polarization hM κ hP hκ
        (M.referencePoint hM κ hP hκ b) b (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) v w).symm
  · exact (M.nativeReferenceTestFieldMarking_kernel hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _)).trans
        (hk.symm.trans (M.transportedNativeReferenceMatrix_kernel hM κ hP hκ f a H z₀ hz₀ z))
  · exact A.complexFiber_embedding_rank κ hκ (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)
      (Complex.BallPeriods.restrictComplexBase_point κ (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))) hP
  · exact B.complexFiber_embedding_rank κ hκ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z).left
      (Complex.BallPeriods.restrictComplexBase_point κ (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)) hP

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
