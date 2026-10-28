import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallArithmetic
import OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

/-! # Intrinsic Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicCoordinates.CM

noncomputable section

/-! Rational symplectic coordinates for the actual total CM tensor
space, with the original trace pairing and native phase order both explicit. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.PhaseCoordinates

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

def nativePhaseSwapEquiv (I R : Type) [Field R] : ((I ⊕ I) → R) ≃ₗ[R] ((I ⊕ I) → R) where
  toFun := RepresentationTheory.Theta.Adelic.DataTheta.swapPhase
  invFun := RepresentationTheory.Theta.Adelic.DataTheta.swapPhase
  left_inv x := by funext i; cases i <;> rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl
  map_smul' c x := by funext i; cases i <;> rfl

theorem native_standard_pairing_swap {I R : Type} [Fintype I] [Field R]
    (x y : (I ⊕ I) → R) : RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase x) (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase y) = -RepresentationTheory.Theta.Adelic.DataTheta.standardPairing x y := by
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.standardPairing, RepresentationTheory.Theta.Adelic.DataTheta.swapPhase, Sum.elim_inl, Sum.elim_inr, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def directSourceTensorEquiv : TransportNew.CM.TensorPositions K ≃ₗ[ℚ] RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.TensorPosition (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2 where
  toFun := QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0
  invFun y i j := QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0 (y (i, j))
  left_inv x := by funext i j; exact (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).apply_symm_apply _
  right_inv y := by funext i; exact (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm_apply_apply _
  map_add' x y := by funext i; exact map_add (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm _ _
  map_smul' c x := by
    funext i
    exact ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm.toLinearEquiv.restrictScalars ℚ).map_smul c (x i.1 i.2)

variable (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)

theorem direct_source_tensor_trace (x y : TransportNew.CM.TensorPositions K) :
    Algebra.trace ℚ (maximalRealSubfield K)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
        (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0).val
        (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 x) (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 y)) =
      -Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K β a x y) := by
  rw [CMGlobalFrames.CM.cm_hermitian_unit_val K δ hδ hδ0, BallArithmetic.CM.directSourceSkewUnit, CMGlobalFrames.CM.cm_skew_unit_val K δ hδ hδ0,
    QuadraticTensor.CM.quadratic_tensor_rational_trace K δ hδ hδ0 β hβ (fun j => -a j) (fun j => by rw [map_neg, ha j])]
  have hn : TransportNew.CM.tensorHermitian K β (fun j => -a j) x y = -TransportNew.CM.tensorHermitian K β a x y := by
    simp only [TransportNew.CM.tensor_hermitian_blocks, neg_mul, Finset.sum_neg_distrib]
  rw [hn, mul_neg, map_neg]

variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 2
  (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0) (BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0))

def directSourceRationalCoordinates :
    TransportNew.CM.TensorPositions K ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℚ) :=
  (((directSourceTensorEquiv K δ hδ hδ0).trans
    ((BallArithmetic.CM.directSourceGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates.restrictScalars ℚ)).trans
      (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A)).trans (nativePhaseSwapEquiv (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℚ)

theorem direct_source_rational_coordinates_pairing (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (directSourceRationalCoordinates K δ hδ hδ0 β hβ hβ0 a ha ha0 A x)
      (directSourceRationalCoordinates K δ hδ hδ0 β hβ hβ0 a ha ha0 A y) =
      Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K β a x y) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A _))
    (RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates A _)) = _
  rw [native_standard_pairing_swap, RepresentationTheory.Theta.Adelic.PhaseCoordinates.rationalPhaseCoordinates_pairing]
  change -Algebra.trace ℚ (maximalRealSubfield K) (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.coordinatePairing 3 2
    ((BallArithmetic.CM.directSourceGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates
      (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 x))
    ((BallArithmetic.CM.directSourceGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.coordinates
      (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 y))) = _
  rw [(BallArithmetic.CM.directSourceGlobalFrames K δ hδ hδ0 a ha ha0 β hβ hβ0).rational.preserves,
    direct_source_tensor_trace, neg_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicCoordinates.CM
