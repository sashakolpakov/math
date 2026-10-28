import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicIndexedGraphs
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourcePeriodAction

/-! # Single Line Period Graph -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLinePeriodGraph.CM

noncomputable section

/-! The period of each actual source line is its fixed rational
symplectic transform in native one-line coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)

def singleSourcePhaseRealization : ((HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℂ) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) :=
  SourceIntrinsicTransition.CM.indexedSwappedPhaseMap (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).complexPhase

theorem direct_single_phase_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    singleSourcePhaseRealization K Q hμ j (fun i => (SingleLineTransition.CM.directSingleIndexedRationalCoordinates K Q hμ j x i : ℂ)) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) := by
  let e := (SingleLineFrame.CM.sourceSingleIndexEquiv K places).sumCongr (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
  let r := SingleLineTrace.CM.directSingleLineRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
  have hi : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => (SingleLineTransition.CM.directSingleIndexedRationalCoordinates K Q hμ j x (e.symm i) : ℂ)) =
      (fun i => ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).rationalPhase
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
  exact (congrArg (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).complexPhase hi).trans
    (SingleLineTransition.CM.direct_single_complex_phase_rational K Q hμ j x)

variable (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

theorem single_source_transition_complex_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j C).map (algebraMap ℚ ℂ) *ᵥ
      (fun i => (CoordinateComparison.CM.sumCoordinates K C x i : ℂ)) =
      fun i => (SingleLineTransition.CM.directSingleIndexedRationalCoordinates K Q hμ j x i : ℂ) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap ℚ ℂ) (SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j C)
    (CoordinateComparison.CM.sumCoordinates K C x) i).symm.trans
      (congrArg (algebraMap ℚ ℂ) (congrFun (SingleLineTransition.CM.single_source_native_transition_apply K Q hμ j C x) i))

theorem single_source_native_complex_transition (w : HeckeCycles.GeometricSource.CM.Ambient K) :
    singleSourcePhaseRealization K Q hμ j
      ((SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j C).map (algebraMap ℚ ℂ) *ᵥ SourceSymplecticAction.CM.sourceComplexSumCoordinates K C w) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j w := by
  let f := (singleSourcePhaseRealization K Q hμ j).comp
    ((Matrix.toLin' ((SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j C).map (algebraMap ℚ ℂ))).comp
      (SourceSymplecticAction.CM.sourceComplexSumCoordinates K C).toLinearMap)
  have he : f = SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j := by
    apply ComplexTransition.CM.linear_maps_eq_of_rational_coordinates (CoordinateComparison.CM.sumCoordinates K C) (SourceSymplecticAction.CM.sourceComplexSumCoordinates K C)
      (HeckeCycles.GeometricSource.CM.embeddingCoordinates K) (SourceSymplecticAction.CM.source_complex_sum_coordinates_embedding K C)
    intro x
    change singleSourcePhaseRealization K Q hμ j
      ((SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j C).map (algebraMap ℚ ℂ) *ᵥ
        SourceSymplecticAction.CM.sourceComplexSumCoordinates K C (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x)) = _
    rw [SourceSymplecticAction.CM.source_complex_sum_coordinates_embedding, single_source_transition_complex_rational, direct_single_phase_rational]
  exact LinearMap.congr_fun he w

def directSingleIndexedPeriod (z : B.Domain) : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (HeckeCycles.GeometricSource.CM.Positions K places) :=
  IntrinsicIndexedGraphs.CM.nativeIndexedPeriod (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

theorem single_source_native_graph_relation (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let α := γ.val.map (algebraMap ℚ ℂ) *ᵥ Sum.elim ((L.period z.val).matrix.mulVec x) x
    (directSingleIndexedPeriod K Q hμ j z).matrix.mulVec (fun i => α (.inr i)) = fun i => α (.inl i) := by
  let w := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x
  let u := HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) w
  have hr : Prescribed.CM.nativePeriodFrame K B places (d j) z.val u = w :=
    AdaptedTotal.CM.native_frame_recovers_line_graph K L z.val z.property x
  have hf := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j) hr).symm.trans
    (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z u)
  have ht := (single_source_native_complex_transition K Q hμ j L.coordinates w).trans hf
  have hp := IntrinsicIndexedGraphs.CM.native_indexed_graph_equation (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j L.coordinates).map (algebraMap ℚ ℂ) *ᵥ
      SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates w) (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u) ht
  simpa only [w, SourcePeriodAction.CM.source_graph_sum_coordinates] using! hp

theorem single_source_native_period_transform (z : B.Domain) :
    directSingleIndexedPeriod K Q hμ j z =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).transformSiegel (L.period z.val) := by
  apply IndexedGraphRelation.CM.symplectic_period_eq_of_graph
  intro x
  exact single_source_native_graph_relation K d Q hμ j L hL z x

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLinePeriodGraph.CM
