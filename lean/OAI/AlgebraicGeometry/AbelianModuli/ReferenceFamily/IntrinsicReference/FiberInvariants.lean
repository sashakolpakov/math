import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.IntrinsicReference.FiberComparison
import OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants

/-! # Fiber Invariants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The reference-to-nearby comparison preserves the exact lattice,
polarization, and every integral CM endomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants

attribute [local implicit_reducible] Complex.BallPeriods.restrictComplexBase
attribute [local irreducible] Models.FinePELModel.complexTestFamily RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm Intrinsic.ChernPairing.nativePolarizationForm

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

theorem Models.FinePELModel.nativeReferenceFiberComparison_integral
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    v ∈ Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety ↔
      M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z v ∈
        Intrinsic.RationalLattice.IntrinsicRationalPeriods.integralPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation (M.complexTestFamily κ f).polarized
          (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)).variety := by
  apply RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integral
  intro w
  exact (M.nativeReferenceTestRationalMarking_integral hM κ hP hκ
    (M.referencePoint hM κ hP hκ b) b (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) w).trans
      (M.transportedNativeReferenceFieldMarking_integral hM κ hP hκ f a H z₀ hz₀ z w).symm

theorem Models.FinePELModel.nativeReferenceFiberComparison_polarization
    (v w : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ f).polarized (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z)
      (M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z v)
      (M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z w) =
        RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.familyPolarizationForm (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
          (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) v w := by
  apply RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_polarization
  intro u t
  exact (M.transportedNativeReferenceFieldMarking_polarization hM κ hP hκ f a H z₀ hz₀ z u t).trans
    (M.nativeReferenceTestRationalMarking_polarization hM κ hP hκ (M.referencePoint hM κ hP hκ b) b
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) (Category.id_comp _) u t).symm

theorem Models.FinePELModel.nativeReferenceFiberComparison_integer (c : NumberField.RingOfIntegers E)
    (v : Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods (RepresentationTheory.Theta.Geometric.PolarizedCanonicalForm.polarizedFamilyPresentation
      (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
      (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase)))).variety) :
    M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z
      (RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).polarized
        (M.complexTestFamily κ (M.referencePoint hM κ hP hκ b)).action
        (𝟙 (Over.mk (𝟙 Foundations.Scheme.ProjectiveSpace.complexBase))) c v) =
      RepresentationTheory.Theta.Geometric.Family.FieldActions.familyIntegralPeriodAction (M.complexTestFamily κ f).polarized (M.complexTestFamily κ f).action
        (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C z) c (M.nativeReferenceFiberComparison hM κ hP hκ f a H z₀ hz₀ b z v) :=
  RepresentationTheory.Theta.Geometric.FieldMarkingPeriodInvariants.fieldMarkingPeriodComparison_integer _ _ _ _ _ _ _ _ c v

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
