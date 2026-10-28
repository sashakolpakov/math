import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFormUniqueness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta

/-! # Reference Theta Class Match -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceThetaClassMatch.CM

noncomputable section

/-! Identify the actual reference theta class with the pullback of a
canonical target class by the derivative chain rule and integration. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
  (Y X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (π : B.Domain → Y.analyticSpace) (c : B.Domain → X.analyticSpace)
  (hπ : ReferenceCover.CM.CoverProperty B.domainOpen Y π)
  (f : C(Y.analyticSpace, X.analyticSpace))
  (hf : ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, X.analyticModel) ∞ f)
  (hcomp : ∀ z, f (π z) = c z)
  (α : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
  (β : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
  (hα : GeometricSource.CM.RepresentsTheta E L φ Y π α) (hβ : GeometricSource.CM.RepresentsTheta E L φ X c β)

include hπ hcomp hα hβ in
theorem forms : AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.pureClosedManifoldFormsPullback f hf 1 0 β = α :=
  CoverFormUniqueness.CM.theta E L φ Y π hπ _ α
    (ReferenceTheta.CM.represents_reference_pullback E L φ X Y c π hπ.2.2.1 f hf hcomp β hβ) hα

include hπ hcomp hα hβ hf in
theorem classes [FiniteDimensional ℚ (Y.rationalCohomology 1)]
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1)) (θX : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 α.val))
    (hθX : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θX =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 β.val)) :
    (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θX = θY := by
  have hforms := congrArg Subtype.val (forms E L φ Y X π c hπ f hf hcomp α β hα hβ)
  apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace Y.toOver) 1
  rw [AnalyticPullback.CM.complexification_pullback, hθX,
    AnalyticPullback.CM.pullback_form_class f hf 1, hθY, ← hforms]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceThetaClassMatch.CM
