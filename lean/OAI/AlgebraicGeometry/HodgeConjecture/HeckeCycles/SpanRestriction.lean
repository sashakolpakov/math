import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ThetaRestriction

/-! # Span Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpanRestriction.CM

noncomputable section

/-! Once extraction holds on the reference component, the actual
holomorphic restriction maps carry it to the original source classes.
The target remains the literal line-image span from HeckeCycles. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction.CM.Construction OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ThetaRestriction.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]
  (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))

/-- The literal CM-line image span is functorial for rational Hodge maps. -/
theorem lineImageSpan_pullback
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (HU : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (HV : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (f : U →ₗ[ℚ] V) (hf : ComplexMultiplication.WeightOne.CM.IsHodgeMap HU HV f)
    {θ : ComplexMultiplication.WeightOne.CM.Complexification U} (hθ : θ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v HU) :
    f.baseChange ℂ θ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v HV := by
  have hspan : MatchedLevelExtraction.CM.Construction.lineImageSpan E v HU ≤ (MatchedLevelExtraction.CM.Construction.lineImageSpan E v HV).comap (f.baseChange ℂ) := by
    apply Submodule.span_le.mpr
    rintro z ⟨g, hg, u, hu, rfl⟩
    apply Submodule.subset_span
    refine ⟨f.comp g, hf.comp hg, u, hu, ?_⟩
    rw [LinearMap.baseChange_comp]
    rfl
  exact hspan hθ

/-- Extraction on a reference theta class gives extraction on its actual
source restriction, with Hodge compatibility and class matching proved. -/
theorem theta_span_restricts
    {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N : ℕ)
    (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π)
    (ρ : B.Domain → Y.analyticSpace)
    (f : C(X.analyticSpace, Y.analyticSpace))
    (hf : ContMDiff 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f)
    (hcomp : ∀ z, f (π z) = ρ z)
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (HY : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (Y.rationalCohomology 1))
    (hX : HX.holomorphic = (X.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1))
    (hY : HY.holomorphic = (Y.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1))
    (source : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (target : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hsource : GeometricSource.CM.RepresentsTheta E L φ X π source)
    (htarget : GeometricSource.CM.RepresentsTheta E L φ Y ρ target)
    (θX : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hθX : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θX =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 source.val))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 target.val))
    (hextract : θY ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v HY) : θX ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v HX := by
  let : FiniteDimensional ℚ (X.rationalCohomology 1) := HX.finiteDimensional
  have hrestrict := Theta.ThetaRestriction.CM.theta_class_restricts E L φ X Y N π hπ ρ f hf hcomp
    source target hsource htarget θX θY hθX hθY
  have hHodge := AnalyticPullback.CM.pullback_isHodgeMap f hf HX HY hX hY
  have h := lineImageSpan_pullback E v HY HX (AnalyticPullback.CM.pullbackQ f 1).hom hHodge hextract
  rwa [hrestrict] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpanRestriction.CM
