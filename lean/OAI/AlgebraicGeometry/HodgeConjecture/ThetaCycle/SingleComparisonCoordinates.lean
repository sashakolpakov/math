import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonRationalTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineTransition

/-! # Single Comparison Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonCoordinates.CM

noncomputable section

/-! Source trace and complex coordinates for an arbitrary valid native
one-line comparison witness. The rational symplectic transition is fixed. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))

def singleComparisonRationalCoordinates :
    HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)) → ℚ) :=
  (SingleLineTrace.CM.directSingleLineTensorEquiv K Q.delta Q.delta_imaginary Q.delta_ne_zero).trans
    (ComparisonRationalTensor.CM.comparisonTensorCoordinates (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
      (SingleLineComponents.CM.directSingleLineFrames K Q j) N)

include hN in
theorem single_comparison_rational_pairing (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (singleComparisonRationalCoordinates K Q hμ j N x)
      (singleComparisonRationalCoordinates K Q hμ j N y) =
        Algebra.trace ℚ K (Q.delta * Q.a j * HeckeCycles.GeometricSource.CM.hermitian K B.b x y) := by
  have h := ComparisonRationalTensor.CM.comparison_tensor_coordinates_pairing_eq (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.directSingleLineFrames K Q j) N hN (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_coordinates _ _)
    (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)
    (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero y)
  exact h.trans (SingleLineTrace.CM.direct_single_line_rational_coordinates_pairing K Q.delta
    Q.delta_imaginary Q.delta_ne_zero (Q.a j) (BallArithmetic.CM.direct_source_a_fixed K Q j)
    (BallArithmetic.CM.direct_source_a_ne_zero K Q j) B.b B.conjugate_b
    (BallArithmetic.CM.direct_source_ball_b_ne_zero K B) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) x y)

def singleComparisonIndexedCoordinates :
    HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[ℚ] ((HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℚ) :=
  (singleComparisonRationalCoordinates K Q hμ j N).trans
    (LinearEquiv.funCongrLeft ℚ ℚ
      ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).sumCongr (SingleLineFrame.CM.sourceSingleIndexEquiv K places)))

include hN in
theorem single_comparison_indexed_pairing (x y : HeckeCycles.GeometricSource.CM.Vec K) :
    RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (singleComparisonIndexedCoordinates K Q hμ j N x)
      (singleComparisonIndexedCoordinates K Q hμ j N y) =
        Algebra.trace ℚ K (Q.delta * Q.a j * HeckeCycles.GeometricSource.CM.hermitian K B.b x y) := by
  let r := singleComparisonRationalCoordinates K Q hμ j N
  have hi : RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (singleComparisonIndexedCoordinates K Q hμ j N x)
      (singleComparisonIndexedCoordinates K Q hμ j N y) = RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (r x) (r y) :=
    Equiv.sum_comp (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (fun i => r x (.inl i) * r y (.inr i) - r x (.inr i) * r y (.inl i))
  exact hi.trans (single_comparison_rational_pairing K Q hμ j N hN x y)

include hN in
theorem single_comparison_complex_phase_rational (x : HeckeCycles.GeometricSource.CM.Vec K) :
    N.complexPhase (fun i => (N.rationalPhase
      ((SingleLineComponents.CM.directSingleLineFrames K Q j).rational.coordinates
        (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) =
      SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j (HeckeCycles.GeometricSource.CM.embeddingCoordinates K x) := by
  have h := ComparisonRationalTensor.CM.comparison_complex_phase_rational_tensor (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.directSingleLineFrames K Q j) N hN
    (SingleLineTrace.CM.singleLineQuadraticPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)
  exact h.trans (SingleLineTransition.CM.direct_single_rational_components K Q hμ j x)

variable (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)

def singleComparisonTransitionMatrix : Matrix (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places)
    (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) ℚ :=
  LinearMap.toMatrix' ((CoordinateComparison.CM.sumCoordinates K C).symm.trans
    (singleComparisonIndexedCoordinates K Q hμ j N)).toLinearMap

theorem single_comparison_transition_apply (x : HeckeCycles.GeometricSource.CM.Vec K) :
    (singleComparisonTransitionMatrix K Q hμ j N C).mulVec (CoordinateComparison.CM.sumCoordinates K C x) =
      singleComparisonIndexedCoordinates K Q hμ j N x := by
  rw [singleComparisonTransitionMatrix, LinearMap.toMatrix'_mulVec]
  change singleComparisonIndexedCoordinates K Q hμ j N
    ((CoordinateComparison.CM.sumCoordinates K C).symm (CoordinateComparison.CM.sumCoordinates K C x)) = _
  rw [LinearEquiv.symm_apply_apply]

include hN in
theorem single_comparison_transition_symplectic (hC : C.a = Q.a j ∧ C.delta = Q.delta) :
    singleComparisonTransitionMatrix K Q hμ j N C ∈
      Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ := by
  apply RepresentationTheory.Hecke.RadialDilation.PairingTransport.Realization.preserving_coordinatePairing_symplectic
  intro x y
  obtain ⟨u, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective x
  obtain ⟨w, rfl⟩ := (CoordinateComparison.CM.sumCoordinates K C).surjective y
  rw [single_comparison_transition_apply, single_comparison_transition_apply,
    single_comparison_indexed_pairing K Q hμ j N hN]
  have h := CoordinateComparison.CM.sumCoordinates_pairing K C u w
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticBasis.Realization.rationalTraceForm_apply, NumberTheory.ArithmeticGroups.Diagonal.CongruenceLevel.trace_matrix_diagonal] at h
  change RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.coordinatePairing (CoordinateComparison.CM.sumCoordinates K C u) (CoordinateComparison.CM.sumCoordinates K C w) =
    Algebra.trace ℚ K (C.delta * C.a * HeckeCycles.GeometricSource.CM.hermitian K B.b u w) at h
  rw [hC.1, hC.2] at h
  exact h.symm

def singleComparisonSymplecticTransition (hC : C.a = Q.a j ∧ C.delta = Q.delta) :
    Matrix.symplecticGroup (HeckeCycles.GeometricSource.CM.Positions K places) ℚ :=
  ⟨singleComparisonTransitionMatrix K Q hμ j N C,
    single_comparison_transition_symplectic K Q hμ j N hN C hC⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonCoordinates.CM
