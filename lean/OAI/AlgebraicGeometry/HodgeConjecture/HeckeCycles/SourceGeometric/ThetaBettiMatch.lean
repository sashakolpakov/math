import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.ThetaBettiClass
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaClassMatch

/-! # Theta Betti Match -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaBettiMatch.CM

noncomputable section

/-! Construct the actual rational Hodge pullback from the GeometricTheta Albanese
to the source reference surface, and identify the original theta class.
No matching or extraction property is added to the source family. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (T : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : T.period = L.period) (hproject : T.project = Theta.Projection.CM.projection E L)
  (hb : T.pel.reference.b = B.b) (hμ : T.pel.reference.μ = E.val.toRingHom)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice T.pel.reference.lattice)

include hperiod hproject hb hμ in
theorem exists_hodge_pullback
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (hg : T.pel.HasIntegralModelGeometry) (hq : T.pel.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : T.pel.RealizesIsogenyQuotient) (hc : T.HasFiniteCoordinates)
    (W : Geometric.ThetaWitness.CM.Witness T hg hq hIsogenyQuotient)
    (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places)) (hφ : Theta.Weil.CM.finiteWeilInput φ ∈ T.sphericalInputs)
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).Domain → Y.analyticSpace)
    (hπ : (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover T.pel.level Y π)
    (α : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (hα : GeometricSource.CM.RepresentsTheta E L φ Y π α)
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 α.val)) :
    ∃ f : C(Y.analyticSpace, W.variety.analyticSpace),
      ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, W.variety.analyticModel) ∞ f ∧
      Function.Surjective f ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (CMExtraction.Intrinsic.Base.nativeH1 T hHodgeDecomposition hg)
        (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation)
        ((AnalyticPullback.CM.pullbackQ f 1).hom.comp (Geometric.ThetaBettiClass.CM.restriction T hg hq hIsogenyQuotient W)) ∧
      (((AnalyticPullback.CM.pullbackQ f 1).hom.comp (Geometric.ThetaBettiClass.CM.restriction T hg hq hIsogenyQuotient W)).baseChange ℂ)
        (Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩) = θY ∧
      ∀ z, f (π z) = Geometric.ThetaReferenceCoverMap.CM.transported E T
        (CoverFactor.CM.withLattice E B T.pel.reference.lattice hΛ.1 hΛ.2.1 hΛ.2.2) hb hμ W.cover z := by
  obtain ⟨f, hf, hs, heq, hcomp⟩ := ThetaClassMatch.CM.exists_matching_map
    E L T hperiod hproject hb hμ hΛ hg hc W.theta W.index W.variety W.component W.cover
    W.uniformization W.canonical φ hφ Y π hπ α hα θY hθY
  have hH := AnalyticPullback.CM.pullback_isHodgeMap f hf
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation)
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition W.variety.presentation)
    (CMExtraction.Naturality.canonicalH1_integral_holomorphic hHodgeDecomposition Y)
    (CMExtraction.Naturality.canonicalH1_integral_holomorphic hHodgeDecomposition W.variety)
  refine ⟨f, hf, hs, hH.comp (Geometric.ThetaBettiClass.CM.restriction_hodge T hg hq hIsogenyQuotient W hHodgeDecomposition), ?_, hcomp⟩
  rw [LinearMap.baseChange_comp]
  change (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ
    ((Geometric.ThetaBettiClass.CM.restriction T hg hq hIsogenyQuotient W).baseChange ℂ
      (Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩)) = θY
  rw [Geometric.ThetaBettiClass.CM.restriction_class]
  exact heq

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaBettiMatch.CM
