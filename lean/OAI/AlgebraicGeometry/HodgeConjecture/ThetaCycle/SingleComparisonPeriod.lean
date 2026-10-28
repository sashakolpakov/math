import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonIndexedGraphs
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourcePeriodAction

/-! # Single Comparison Period -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonPeriod.CM

noncomputable section

/-! The actual source period is the fixed symplectic transform in any
native coordinates satisfying the full comparison propositions. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))

def singleComparisonPhaseRealization : ((HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℂ) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) :=
  SourceIntrinsicTransition.CM.indexedSwappedPhaseMap (SingleLineFrame.CM.sourceSingleIndexEquiv K places) N.complexPhase

include hN in
theorem single_comparison_phase_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    singleComparisonPhaseRealization K Q hμ j N (fun i => (SingleComparisonCoordinates.CM.singleComparisonIndexedCoordinates K Q hμ j N x i : ℂ)) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) := by
  let e := (SingleLineFrame.CM.sourceSingleIndexEquiv K places).sumCongr (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
  let r := SingleComparisonCoordinates.CM.singleComparisonRationalCoordinates K Q hμ j N
  have hi : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (SingleComparisonCoordinates.CM.singleComparisonIndexedCoordinates K Q hμ j N x (e.symm i) : ℂ)) =
      (fun i => (N.rationalPhase
        ((SingleLineComponents.CM.directSingleLineFrames K Q j).rational.coordinates
          (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) := by
    refine funext (fun i : (Fin places.count × (Fin 3 × Fin 1)) ⊕ (Fin places.count × (Fin 3 × Fin 1)) => ?_)
    cases i with
    | inl i =>
      change ((r x (e (e.symm (.inr i))) : ℚ) : ℂ) = ((r x (.inr i) : ℚ) : ℂ)
      exact congrArg (fun k => ((r x k : ℚ) : ℂ)) (e.apply_symm_apply (.inr i))
    | inr i =>
      change ((r x (e (e.symm (.inl i))) : ℚ) : ℂ) = ((r x (.inl i) : ℚ) : ℂ)
      exact congrArg (fun k => ((r x k : ℚ) : ℂ)) (e.apply_symm_apply (.inl i))
  exact (congrArg N.complexPhase hi).trans
    (SingleComparisonCoordinates.CM.single_comparison_complex_phase_rational K Q hμ j N hN x)

variable (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

theorem single_comparison_transition_complex_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N C).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => (CoordinateComparison.CM.sumCoordinates K C x i : ℂ)) =
      fun i => (SingleComparisonCoordinates.CM.singleComparisonIndexedCoordinates K Q hμ j N x i : ℂ) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N C)
    (CoordinateComparison.CM.sumCoordinates K C x) i).symm.trans
      (congrArg (algebraMap ℚ ℂ) (congrFun (SingleComparisonCoordinates.CM.single_comparison_transition_apply K Q hμ j N C x) i))

include hN in
theorem single_comparison_complex_transition (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    singleComparisonPhaseRealization K Q hμ j N
      ((SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N C).map (algebraMap ℚ ℂ) *ᵥ SourceSymplecticAction.CM.sourceComplexSumCoordinates K C w) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j w := by
  let f := (singleComparisonPhaseRealization K Q hμ j N).comp
    ((Matrix.toLin' ((SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N C).map (algebraMap ℚ ℂ))).comp
      (SourceSymplecticAction.CM.sourceComplexSumCoordinates K C).toLinearMap)
  have he : f = SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (CoordinateComparison.CM.sumCoordinates K C) (SourceSymplecticAction.CM.sourceComplexSumCoordinates K C)
      (HeckeCycles.GeometricSource.CM.embeddingCoordinates K) (SourceSymplecticAction.CM.source_complex_sum_coordinates_embedding K C)
    intro x
    change singleComparisonPhaseRealization K Q hμ j N
      ((SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N C).map (algebraMap ℚ ℂ) *ᵥ
        SourceSymplecticAction.CM.sourceComplexSumCoordinates K C (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x)) = _
    rw [SourceSymplecticAction.CM.source_complex_sum_coordinates_embedding, single_comparison_transition_complex_rational,
      single_comparison_phase_rational K Q hμ j N hN]
  exact LinearMap.congr_fun he w

def singleComparisonIndexedPeriod (z : B.Domain) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places) :=
  ComparisonIndexedGraphs.CM.comparisonIndexedPeriod N
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

include hG in
theorem single_comparison_graph_relation (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
    let α := γ.val.map (algebraMap ℚ ℂ) *ᵥ Sum.elim ((L.period z.val).matrix.mulVec x) x
    (singleComparisonIndexedPeriod K Q hμ j N z).matrix.mulVec (fun i => α (.inr i)) = fun i => α (.inl i) := by
  let w := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x
  let u := HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) w
  have hr : Prescribed.CM.nativePeriodFrame K B places (d j) z.val u = w :=
    AdaptedTotal.CM.native_frame_recovers_line_graph K L z.val z.property x
  have hf := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j) hr).symm.trans
    (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z u)
  have ht := (single_comparison_complex_transition K Q hμ j N hN L.coordinates w).trans hf
  have hp := ComparisonIndexedGraphs.CM.comparison_indexed_graph_equation N hG
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N L.coordinates).map (algebraMap ℚ ℂ) *ᵥ
      SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates w) (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u) ht
  simpa only [w, SourcePeriodAction.CM.source_graph_sum_coordinates] using! hp

include hG in
theorem single_comparison_period_transform (z : B.Domain) :
    singleComparisonIndexedPeriod K Q hμ j N z =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).transformSiegel (L.period z.val) := by
  apply IndexedGraphRelation.CM.symplectic_period_eq_of_graph
  intro x
  exact single_comparison_graph_relation K d Q hμ j N hN hG L hL z x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonPeriod.CM
