import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaBettiMatch
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpanRestriction

/-! # Theta Restriction Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRestrictionExtraction.CM

noncomputable section

/-! Pull extraction on the actual GeometricTheta theta class back to the actual
original reference theta class through the constructed rational Hodge map. -/

open scoped Classical _root_.NumberField _root_.Manifold ContDiff TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)
  {K : Type} [Field K] [NumberField K] {q : ℕ} [Fact q.Prime]
  {Ga MpR MpF MpA : Type} [Group Ga] [TopologicalSpace Ga]
  [Group MpR] [Group MpF] [Group MpA]
  (T : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K places.count q (GeometricSource.CM.Positions E places) Ga MpR MpF MpA)
  (hperiod : T.period = L.period) (hproject : T.project = Theta.Projection.CM.projection E L)
  (hb : T.pel.reference.b = B.b) (hμ : T.pel.reference.μ = E.val.toRingHom)
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice T.pel.reference.lattice)

variable (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))

include hperiod hproject hb hμ in
theorem reference_extraction
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
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 α.val))
    (hextract : Geometric.ThetaBettiClass.CM.classMap T hg hq hIsogenyQuotient W
      ⟨Theta.Weil.CM.finiteWeilInput φ, hφ⟩ ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (CMExtraction.Intrinsic.Base.nativeH1 T hHodgeDecomposition hg)) :
    θY ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v
      (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation) := by
  obtain ⟨f, _hf, _hs, hH, hθ, _hcomp⟩ := ThetaBettiMatch.CM.exists_hodge_pullback
    E L T hperiod hproject hb hμ hΛ hHodgeDecomposition hg hq hIsogenyQuotient hc W φ hφ Y π hπ α hα θY hθY
  have h := SpanRestriction.CM.lineImageSpan_pullback E v (CMExtraction.Intrinsic.Base.nativeH1 T hHodgeDecomposition hg)
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation)
    ((AnalyticPullback.CM.pullbackQ f 1).hom.comp (Geometric.ThetaBettiClass.CM.restriction T hg hq hIsogenyQuotient W)) hH hextract
  exact hθ ▸ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceGeometric.ThetaRestrictionExtraction.CM
