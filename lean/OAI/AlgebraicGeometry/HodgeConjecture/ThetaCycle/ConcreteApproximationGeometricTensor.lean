import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationNormalized
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FrameDualTransport
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalAdaptedDualSlots

/-! # Concrete Approximation Geometric Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor.CM

noncomputable section

/-! The full native geometric tensor evaluates the literal split-source
tensor on fixed dual adapted coordinates. This includes the actual
cotangent slots used in the source two-form. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem inverse_half_frame_cancel (q f c s t : ℂ) (hq : q ≠ 0) :
    q⁻¹ * (f * (c * (q * s)) * t) = f * c * s * t := by
  field_simp

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationNativeDualCoordinates (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    Fin D.places.count × (Fin 3 × Fin 2) → ℂ :=
  fun j => (ConcreteApproximationFrameDeterminant.CM.approximationIndexedFrameCoefficientMatrix K D A hid)⁻¹ᵀ.mulVec u
    ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm j)

theorem approximation_native_jacobi_adapted (z : D.ball.Domain)
    (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    ConcreteApproximationNormalized.CM.approximationNativeJacobi K D A hid z.val
      ((SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val)ᵀ.mulVec u) =
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).invᵀ.mulVec
        (approximationNativeDualCoordinates K D A hid u) := by
  have hG : IsUnit (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val).det := by
    rw [SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
  have h := FrameDualTransport.CM.frame_inverse_transpose_cancel _ _ _ _ _
    (ConcreteApproximationFrameDeterminant.CM.approximation_native_frame_denominator_matrix K D A hid z) hG u
  have hi := congrArg (fun x : PeriodTotal.CM.TotalPositions K D.places → ℂ =>
    fun j => x ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm j)) h
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
    ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).val
    ((ConcreteApproximationFrameDeterminant.CM.approximationIndexedFrameCoefficientMatrix K D A hid)⁻¹ᵀ.mulVec u)
  have he := hi.trans hr
  have hinv := Matrix.coe_units_inv
    ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z))
  have hf := congrArg (fun M : Matrix (Fin D.places.count × (Fin 3 × Fin 2))
      (Fin D.places.count × (Fin 3 × Fin 2)) ℂ =>
    Mᵀ.mulVec (approximationNativeDualCoordinates K D A hid u)) hinv
  simpa only [ConcreteApproximationNormalized.CM.approximationNativeJacobi, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply] using! he.trans hf.symm

theorem approximation_native_geometric_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z₀ z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (fun j => approximationNativeDualCoordinates K D A hid (u j)) =
      ((Nat.factorial a : ℂ)⁻¹) * ConcreteApproximationFrameDeterminant.CM.approximationNativeHalfRatio K D A hid z₀ *
        (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ)) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
          (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val))) 0
          (fun j => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val)ᵀ.mulVec (u j)) := by
  let N := ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid
  let q := N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
  have hq : q ≠ 0 :=
    (mul_ne_zero_iff.mp (ConcreteApproximationFrameDeterminant.CM.approximation_native_half_denominator_ne_zero K D A hid z)).1
  have hj : (fun j => ConcreteApproximationNormalized.CM.approximationNativeJacobi K D A hid z.val
      ((SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val)ᵀ.mulVec (u j))) =
      (fun j => (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).invᵀ.mulVec
        (approximationNativeDualCoordinates K D A hid (u j))) :=
    funext (fun j => approximation_native_jacobi_adapted K D A hid z (u j))
  have ht := ConcreteApproximationNormalized.CM.approximation_split_native_completed_tensor K D A hid φ z₀ z a
    (fun j => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val)ᵀ.mulVec (u j))
  rw [hj] at ht
  have hs := congrArg (fun c : ℂ => q⁻¹ * c) ht
  exact hs.trans (inverse_half_frame_cancel _ _ _ _ _ hq)

theorem approximation_native_geometric_source_slots (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z₀ z : D.ball.Domain) (a b : Fin 2 × Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ) 2
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
      ![approximationNativeDualCoordinates K D A hid (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places a),
        approximationNativeDualCoordinates K D A hid (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places b)] =
      (2 : ℂ)⁻¹ * ConcreteApproximationFrameDeterminant.CM.approximationNativeHalfRatio K D A hid z₀ *
        InitialTensor.CM.splitThetaTensor K (A.periods 0) (A.periods 1) (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) z.val a b := by
  have h := approximation_native_geometric_tensor K D A hid φ z₀ z 2
    ![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places b]
  have hu : (fun j : Fin 2 => approximationNativeDualCoordinates K D A hid
      (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places b] j)) =
      ![approximationNativeDualCoordinates K D A hid (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places a),
        approximationNativeDualCoordinates K D A hid (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places b)] := by
    funext j
    fin_cases j <;> rfl
  have hv : (fun j : Fin 2 => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val)ᵀ.mulVec
      (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K D.places b] j)) =
      ![InitialTensor.CM.splitThetaSlot K (A.periods 0) (A.periods 1) z.val a,
        InitialTensor.CM.splitThetaSlot K (A.periods 0) (A.periods 1) z.val b] := by
    funext j
    fin_cases j
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K A.periods z.val a).symm
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K A.periods z.val b).symm
  rw [hu, hv, show (Nat.factorial 2 : ℂ) = 2 from by norm_num] at h
  simpa only [InitialTensor.CM.splitThetaTensor, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor.CM
