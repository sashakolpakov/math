import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleAdaptedDualSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor

/-! # Single Line Geometric Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor.CM

noncomputable section

/-! The full native tensor of the fixed one-line input equals the actual
source tensor on constant dual coordinates, including the literal
cotangent coefficients of the source one-form. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem single_frame_inverse_transpose_cancel {I : Type} [Fintype I] [DecidableEq I]
    (J F C G : Matrix I I ℂ) (h : J = F * C * G) (hG : IsUnit G.det) (u : I → ℂ) :
    J⁻¹ᵀ.mulVec (Gᵀ.mulVec u) = F⁻¹ᵀ.mulVec (C⁻¹ᵀ.mulVec u) := by
  have he : J * 1 = F * C * G := (mul_one J).trans h
  simpa only [inv_one, Matrix.transpose_one, Matrix.one_mulVec] using
    FrameDualTransport.CM.frame_inverse_transpose_cancel J 1 F C G he hG u

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def directSingleNativeDualCoordinates (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    Fin places.count × (Fin 3 × Fin 1) → ℂ :=
  fun k => (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j)⁻¹ᵀ.mulVec u
    ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)

theorem single_source_native_jacobi_adapted (z : B.Domain) (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    (fun k => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).jacobiChange
      (L.period z.val) ((SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec u)
        ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)) =
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (directSingleNativeDualCoordinates K d Q j u) := by
  have hG : IsUnit (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val).det := by
    rw [SourceHalfDetAction.CM.source_adapted_graph_matrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (Units.ne_zero _))
  have h := single_frame_inverse_transpose_cancel _ _ _ _
    (SingleLineFrameDeterminant.CM.single_source_native_frame_denominator_matrix K d Q hμ j L hL z) hG u
  have hi := congrArg (fun x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ =>
    fun k => x ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)) h
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    ((SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j)⁻¹ᵀ.mulVec u)
  have he := hi.trans hr
  have hinv := Matrix.coe_units_inv ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
  have hf := congrArg (fun M : Matrix (Fin places.count × (Fin 3 × Fin 1))
      (Fin places.count × (Fin 3 × Fin 1)) ℂ =>
    Mᵀ.mulVec (directSingleNativeDualCoordinates K d Q j u)) hinv
  simpa only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply] using! he.trans hf.symm

theorem single_source_native_geometric_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (z₀ z : B.Domain) (a : ℕ) (u : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (fun k => directSingleNativeDualCoordinates K d Q j (u k)) =
      ((Nat.factorial a : ℂ)⁻¹) * SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀ *
        (L.halfDet z.val : ℂ) * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z.val)) 0
          (fun k => (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k)) := by
  let N := SingleLineComponents.CM.directSingleLineComparison K Q hμ j
  let q := N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hq : q ≠ 0 :=
    (mul_ne_zero_iff.mp (SingleLineHalfRatio.CM.single_source_native_half_denominator_ne_zero K d Q hμ j L z)).1
  have hj : (fun k i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).jacobiChange
      (L.period z.val) ((SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
        ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      (fun k => (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (directSingleNativeDualCoordinates K d Q j (u k))) :=
    funext (fun k => single_source_native_jacobi_adapted K d Q hμ j L hL z (u k))
  have ht := SingleLineComparison.CM.single_source_native_completed_tensor K d Q hμ j L hL φ z₀ z a
    (fun k => (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
  have hx := congrArg (RepresentationTheory.Theta.Adelic.DataTheta.completedTensor N
    (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) hj
  have hs := congrArg (fun c : ℂ => q⁻¹ * c) (hx.symm.trans ht)
  exact hs.trans (ConcreteApproximationGeometricTensor.CM.inverse_half_frame_cancel _ _ _ _ _ hq)

theorem single_source_native_geometric_source_slot (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (z₀ z : B.Domain) (i : Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (SingleLineComparison.CM.directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) 1
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (fun _ => directSingleNativeDualCoordinates K d Q j (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)) =
      SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀ * Slots.CM.sourceThetaCoordinates K L φ z.val i := by
  have h := single_source_native_geometric_tensor K d Q hμ j L hL φ z₀ z 1
    (fun _ => SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedFDeriv_one_apply,
    ← SingleAdaptedDualSlots.CM.theta_jacobi_slot_adapted_transpose] at h
  exact h.trans (by rw [Slots.CM.source_coordinates_completed_slots]; exact mul_assoc _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor.CM
