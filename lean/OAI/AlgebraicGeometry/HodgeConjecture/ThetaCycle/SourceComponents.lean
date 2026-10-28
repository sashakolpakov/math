import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComplexTransition

/-! # Source Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceComponents.CM

noncomputable section

/-! The original paired CM embeddings of the total tensor space are
exactly the native complex tensor realization after its explicit normalization. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def sourcePairedTensorCoordinates (places : HeckeCycles.GeometricSource.CM.Places K) :
    ComplexTransition.CM.TotalAmbient K →ₗ[ℂ]
      (Fin places.count → ((Fin 3 × Fin 2 → ℂ) × (Fin 3 × Fin 2 → ℂ))) where
  toFun w v :=
    (fun ij => (Symplectic.CM.galoisToPaired K places (w ij.2) v).1 ij.1,
     fun ij => (Symplectic.CM.galoisToPaired K places (w ij.2) v).2 ij.1)
  map_add' x y := by
    funext v
    apply Prod.ext
    · funext ij
      exact congrArg (fun u => (u v).1 ij.1) (map_add (Symplectic.CM.galoisToPaired K places) (x ij.2) (y ij.2))
    · funext ij
      exact congrArg (fun u => (u v).2 ij.1) (map_add (Symplectic.CM.galoisToPaired K places) (x ij.2) (y ij.2))
  map_smul' c x := by
    funext v
    apply Prod.ext
    · funext ij
      exact congrArg (fun u => (u v).1 ij.1) (map_smul (Symplectic.CM.galoisToPaired K places) c (x ij.2))
    · funext ij
      exact congrArg (fun u => (u v).2 ij.1) (map_smul (Symplectic.CM.galoisToPaired K places) c (x ij.2))

theorem source_paired_tensor_embedding (places : HeckeCycles.GeometricSource.CM.Places K) (x : TransportNew.CM.TensorPositions K) :
    sourcePairedTensorCoordinates K places (ComplexTransition.CM.totalEmbedding K x) =
      fun v => (fun ij => HeckeCycles.ReferenceDatum.CM.embeddings K places v (x ij.1 ij.2),
        fun ij => star (HeckeCycles.ReferenceDatum.CM.embeddings K places v (x ij.1 ij.2))) := by
  funext v
  apply Prod.ext
  · funext ij
    exact congrArg (fun w => (w v).1 ij.1)
      (Symplectic.CM.galoisToPaired_embedding K places (fun j => x j ij.2))
  · funext ij
    exact congrArg (fun w => (w v).2 ij.1)
      (Symplectic.CM.galoisToPaired_embedding K places (fun j => x j ij.2))

variable {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  {d : Fin 2 → Fin places.count → Bool} (Q : Lagrangians.CM.LagrangianPair K B places d)
  (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

abbrev directSourceFrames :=
  BallArithmetic.CM.directSourceGlobalFrames K Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) B.b B.conjugate_b
    (BallArithmetic.CM.direct_source_ball_b_ne_zero K B)

abbrev directSourceComparison :=
  RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (directSourceFrames K Q)

def directSourceComplexComponents :
    ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] RepresentationTheory.Theta.Adelic.BallGeometryData.ComplexPhase (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) :=
  (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)).comp
    (sourcePairedTensorCoordinates K places)

theorem direct_source_rational_components (x : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) (.inl (RealPlaces.CM.sourceRealPlaces K places v))
        (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x j)) =
      directSourceComplexComponents K Q hμ hother (ComplexTransition.CM.totalEmbedding K x) := by
  change _ = IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (sourcePairedTensorCoordinates K places (ComplexTransition.CM.totalEmbedding K x))
  rw [source_paired_tensor_embedding]
  apply IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values
  intro v j
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K places Q.delta Q.delta_imaginary Q.delta_ne_zero v
    (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x j)).trans
    (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K places v)
      ((QuadraticModel.CM.cmQuadraticEquiv K Q.delta Q.delta_imaginary Q.delta_ne_zero).apply_symm_apply _))

theorem direct_source_complex_phase_rational (x : TransportNew.CM.TensorPositions K) :
    (directSourceComparison K Q hμ hother).complexPhase
      (fun i => ((directSourceComparison K Q hμ hother).rationalPhase
        ((directSourceFrames K Q).rational.coordinates
          (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) =
      directSourceComplexComponents K Q hμ hother (ComplexTransition.CM.totalEmbedding K x) := by
  have h := IntrinsicTensorComplexCoordinates.CM.native_complex_phase_rational_tensor (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (directSourceFrames K Q)
    (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)
  have hh := h.trans (direct_source_rational_components K Q hμ hother x)
  unfold directSourceComparison
  exact hh

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceComponents.CM
