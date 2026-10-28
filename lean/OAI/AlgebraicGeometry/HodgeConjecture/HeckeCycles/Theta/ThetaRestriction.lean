import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching

/-! # Theta Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ThetaRestriction.CM

noncomputable section

/-! Restriction matches the actual source theta class. The commuting
equation between the coverings, the derivative chain rule, and canonical
integration identify the pulled-back reference form with the original one. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
  (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ)
  (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
  (ρ : B.Domain → Y.analyticSpace)
  (f : C(X.analyticSpace, Y.analyticSpace))
  (hf : ContMDiff 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f)
  (hcomp : ∀ z, f (π z) = ρ z)

include hπ hcomp hf

/-- The pullback of the reference theta form satisfies the source's
literal theta-derivative equation. -/
theorem represents_pullback
    (form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hform : GeometricSource.CM.RepresentsTheta E L φ Y ρ form) :
    GeometricSource.CM.RepresentsTheta E L φ X π (AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.pureClosedManifoldFormsPullback f hf 1 0 form) := by
  intro z ξ
  have heq : (f : X.analyticSpace → Y.analyticSpace) ∘ π = ρ := funext hcomp
  have hderiv : mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, Y.analyticModel) ρ z =
      (mfderiv 𝓘(ℝ, X.analyticModel) 𝓘(ℝ, Y.analyticModel) f (π z)).comp
        (mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z) := by
    rw [← heq]
    exact mfderiv_comp z
      ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf).mdifferentiable (by decide) (π z))
      (Matching.CM.mdifferentiableAt_real (hπ.2.2.2.1 z))
  change form.val.val.val (f (π z))
    (fun _ : Fin 1 => mfderiv 𝓘(ℝ, X.analyticModel) 𝓘(ℝ, Y.analyticModel) f (π z)
      (mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z ξ)) = _
  rw [hcomp z]
  convert hform z ξ using 1
  rw [hderiv]
  rfl

/-- Canonical rational-complexified cohomology recovers the original
theta class under the actual continuous pullback. -/
theorem theta_class_restricts
    [FiniteDimensional ℚ (X.rationalCohomology 1)]
    (source : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (target : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hsource : GeometricSource.CM.RepresentsTheta E L φ X π source)
    (htarget : GeometricSource.CM.RepresentsTheta E L φ Y ρ target)
    (θX : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hθX : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θX =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 source.val))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 target.val)) :
    (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θY = θX := by
  have hrep := represents_pullback E L φ X Y N π hπ ρ f hf hcomp target htarget
  have hforms := Matching.CM.representsTheta_unique E L φ X N π hπ source
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.pureClosedManifoldFormsPullback f hf 1 0 target) hsource hrep
  have hval : source.val =
      Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf) 1 target.val :=
    congrArg Subtype.val hforms
  apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace X.toOver) 1
  rw [AnalyticPullback.CM.complexification_pullback, hθY,
    AnalyticPullback.CM.pullback_form_class f hf 1, hθX, hval]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ThetaRestriction.CM
