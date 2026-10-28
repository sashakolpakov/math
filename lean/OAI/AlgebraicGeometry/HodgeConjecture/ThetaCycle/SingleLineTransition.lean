import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrame
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicTransition
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceSymplecticAction

/-! # Single Line Transition -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTransition.CM

noncomputable section

/-! The transition from each actual source line's rational coordinates
to its native coordinates is a fixed rational symplectic matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)

def directSingleIndexedRationalCoordinates : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] ((HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℚ) :=
  (SingleLineTrace.CM.directSingleLineRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)).trans
      (LinearEquiv.funCongrLeft ℚ ℚ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).sumCongr (SingleLineFrame.CM.sourceSingleIndexEquiv K places)))

theorem direct_single_indexed_pairing (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (directSingleIndexedRationalCoordinates K Q hμ j x)
      (directSingleIndexedRationalCoordinates K Q hμ j y) =
      Algebra.trace ℚ K (Q.delta * Q.a j * HeckeCycles.GeometricSource.CM.hermitian K B.b x y) := by
  let r := SingleLineTrace.CM.directSingleLineRationalCoordinates K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a j)
    (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
  have hi : RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (directSingleIndexedRationalCoordinates K Q hμ j x)
      (directSingleIndexedRationalCoordinates K Q hμ j y) = RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (r x) (r y) :=
    Equiv.sum_comp (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (fun i => r x (.inl i) * r y (.inr i) - r x (.inr i) * r y (.inl i))
  exact hi.trans (SingleLineTrace.CM.direct_single_line_rational_coordinates_pairing K Q.delta Q.delta_imaginary Q.delta_ne_zero
    (Q.a j) (BallArithmetic.CM.direct_source_a_fixed K Q j) (BallArithmetic.CM.direct_source_a_ne_zero K Q j)
    B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) x y)

theorem single_source_paired_embedding (x : HeckeCycles.GeometricSource.CM.Vec K) :
    SingleLineComponents.CM.singleSourcePairedCoordinates K places (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) =
      fun v => (fun i : Fin 3 × Fin 1 => HeckeCycles.ReferenceDatum.CM.embeddings K places v (x i.1),
        fun i : Fin 3 × Fin 1 => star (HeckeCycles.ReferenceDatum.CM.embeddings K places v (x i.1))) := by
  funext v
  apply Prod.ext
  · funext i
    exact congrArg (fun w => (w v).1 i.1) (Symplectic.CM.galoisToPaired_embedding K places x)
  · funext i
    exact congrArg (fun w => (w v).2 i.1) (Symplectic.CM.galoisToPaired_embedding K places x)

theorem direct_single_rational_components (x : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
      (fun v i => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) (.inl (RealPlaces.CM.sourceRealPlaces K places v))
        (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x i)) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) := by
  change _ = IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.singleSourcePairedCoordinates K places (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x))
  rw [single_source_paired_embedding]
  apply IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values
  intro v i
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K places Q.delta Q.delta_imaginary Q.delta_ne_zero v
    (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x i)).trans
      (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K places v) ((QuadraticModel.CM.cmQuadraticEquiv K Q.delta Q.delta_imaginary Q.delta_ne_zero).apply_symm_apply _))

theorem direct_single_complex_phase_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).complexPhase
      (fun i => ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).rationalPhase
        ((SingleLineComponents.CM.directSingleLineFrames K Q j).rational.coordinates
          (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) := by
  have h := IntrinsicTensorComplexCoordinates.CM.native_complex_phase_rational_tensor (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)
  exact h.trans (direct_single_rational_components K Q hμ j x)

variable (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

def singleSourceNativeTransitionMatrix : Matrix (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places)
    (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) ℚ :=
  LinearMap.toMatrix' ((CoordinateComparison.CM.sumCoordinates K C).symm.trans (directSingleIndexedRationalCoordinates K Q hμ j)).toLinearMap

theorem single_source_native_transition_apply (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (singleSourceNativeTransitionMatrix K Q hμ j C).mulVec (CoordinateComparison.CM.sumCoordinates K C x) =
      directSingleIndexedRationalCoordinates K Q hμ j x := by
  rw [singleSourceNativeTransitionMatrix, LinearMap.toMatrix'_mulVec]
  change directSingleIndexedRationalCoordinates K Q hμ j ((CoordinateComparison.CM.sumCoordinates K C).symm (CoordinateComparison.CM.sumCoordinates K C x)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem single_source_native_transition_symplectic (hC : C.a = Q.a j ∧ C.delta = Q.delta) :
    singleSourceNativeTransitionMatrix K Q hμ j C ∈ Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  obtain ⟨u, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective x
  obtain ⟨w, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective y
  rw [single_source_native_transition_apply, single_source_native_transition_apply, direct_single_indexed_pairing]
  have h := CoordinateComparison.CM.sumCoordinates_pairing K C u w
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal] at h
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (CoordinateComparison.CM.sumCoordinates K C u) (CoordinateComparison.CM.sumCoordinates K C w) =
    Algebra.trace ℚ K (C.delta * C.a * HeckeCycles.GeometricSource.CM.hermitian K B.b u w) at h
  rw [hC.1, hC.2] at h
  exact h.symm

def singleSourceNativeSymplecticTransition (hC : C.a = Q.a j ∧ C.delta = Q.delta) :
    Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ :=
  ⟨singleSourceNativeTransitionMatrix K Q hμ j C, single_source_native_transition_symplectic K Q hμ j C hC⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTransition.CM
