import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicPairedAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComplexComponents
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameAction

/-! # Concrete Approximation Group Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGroupAction.CM

noncomputable section

/-! The actual source special-unitary action on both multiplicity lines
is the native geometric action on the fixed approximation tensor space.
It commutes with the given rational multiplicity basis change. -/

open scoped Classical _root_.NumberField _root_.Matrix Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.TensorGeometricAction
open _root_.Module

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem tensor_first_star_mulVec {m : ℕ} (M : Matrix (Fin 3) (Fin 3) ℂ)
    (x : Fin 3 × Fin m → ℂ) (i : Fin 3) (j : Fin m) :
    ((M ⊗ₖ (1 : Matrix (Fin m) (Fin m) ℂ)).map star).mulVec x (i, j) =
      (M.map star).mulVec (fun k => x (k, j)) i := by
  simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def totalBallAmbientAction (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) : ComplexTransition.CM.TotalAmbient K →ₗ[ℂ] ComplexTransition.CM.TotalAmbient K :=
  LinearMap.pi (fun j => (SourceSymplecticAction.CM.ballAmbientAction K g).comp (LinearMap.proj j))

omit [NumberField K] [IsCMField K] in
theorem total_ball_action_basis_commute (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (b : Basis (Fin 2) K (Analysis.DifferentialForms.Coordinates.LocalApproximation.W K)) (w : ComplexTransition.CM.TotalAmbient K) :
    totalBallAmbientAction K g (ComplexTransition.CM.complexTensorBasisChange K b w) =
      ComplexTransition.CM.complexTensorBasisChange K b (totalBallAmbientAction K g w) := by
  funext j τ i
  change (∑ k, SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ i k * ∑ l : Fin 2, (τ (b l j) : ℂ) * w l τ k) =
    ∑ l : Fin 2, (τ (b l j) : ℂ) * ∑ k, SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ i k * w l τ k
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ball_embedding_matrix_conjugate (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (τ : Gal(K/ℚ)) :
    SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) = (SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ).map star := by
  apply Matrix.ext
  intro i j
  change ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) (LinearMap.toMatrix' g.toLinearMap i j) = _
  rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation]
  rfl

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g)

theorem approximation_native_unnormalized_matrix (τ : Fin D.places.count) :
    IntrinsicPairedAction.CM.nativeUnnormalizedTensorMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
      (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg) τ =
      SourceSymplecticAction.CM.ballEmbeddingMatrix K g (D.places.representative τ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hm := SourceIntrinsicLine.CM.direct_source_rational_local_matrix K D.pair N g hg τ
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) hm

theorem approximation_source_paired_action (w : ComplexTransition.CM.TotalAmbient K) :
    SourceComponents.CM.sourcePairedTensorCoordinates K D.places (totalBallAmbientAction K g w) =
      IntrinsicPairedAction.CM.nativePairedActionLinear (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
        (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w) := by
  refine funext (fun τ : Fin D.places.count => ?_)
  apply Prod.ext
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ =>
      M.mulVec (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).1 ij)
      (approximation_native_unnormalized_matrix K D A hid N g hg τ)
    have he := RepresentationTheory.Theta.Adelic.TensorGeometricAction.tensor_first_mulVec (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (D.places.representative τ))
      (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).1 ij.1 ij.2
    have hs := congrArg (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.1 ij.1)
      (SourceFrameAction.CM.ball_ambient_action_paired K D.places g (w ij.2) τ)
    exact hs.trans (hm.trans he).symm
  · funext ij
    have hm := congrArg (fun M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ =>
      (M.map star).mulVec (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).2 ij)
      (approximation_native_unnormalized_matrix K D A hid N g hg τ)
    have he := tensor_first_star_mulVec (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (D.places.representative τ))
      (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).2 ij.1 ij.2
    have hc := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
      M.mulVec (fun k => (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w τ).2 (k, ij.2)) ij.1)
      (ball_embedding_matrix_conjugate K g (D.places.representative τ))
    have hs := congrArg (fun p : (Fin 3 → ℂ) × (Fin 3 → ℂ) => p.2 ij.1)
      (SourceFrameAction.CM.ball_ambient_action_paired K D.places g (w ij.2) τ)
    exact hs.trans (hc.trans (hm.trans he).symm)

theorem approximation_complex_components_action (w : ComplexTransition.CM.TotalAmbient K) :
    ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid (totalBallAmbientAction K g w) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
        (ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid w) :=
  (congrArg (IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid))
    (approximation_source_paired_action K D A hid N g hg w)).trans
      (IntrinsicPairedAction.CM.native_paired_components_action (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
        (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg) (SourceComponents.CM.sourcePairedTensorCoordinates K D.places w))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGroupAction.CM
