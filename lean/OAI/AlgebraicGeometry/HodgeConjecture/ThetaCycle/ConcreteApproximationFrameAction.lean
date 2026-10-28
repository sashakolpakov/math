import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGroupAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor
import OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle

/-! # Concrete Approximation Frame Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction.CM

noncomputable section

section

/-! The constant source/native frame comparison intertwines the actual
principal group action. The source action retains both multiplicity
lines and every CM-place block. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance
open OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def totalSourceFrameMatrix (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ :=
  Matrix.fromBlocks (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places (d 0) z) 0 0
    (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places (d 1) z)

theorem total_source_frame_matrix_mulVec
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool) (z : HeckeCycles.GeometricSource.CM.BallChart)
    (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    (totalSourceFrameMatrix K g hdet B places d z).mulVec x =
      Sum.elim ((SourceFrameAction.CM.sourceFrameMatrix K g hdet B places (d 0) z).mulVec (fun p => x (.inl p)))
        ((SourceFrameAction.CM.sourceFrameMatrix K g hdet B places (d 1) z).mulVec (fun p => x (.inr p))) := by
  simp only [totalSourceFrameMatrix, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add]
  rfl

theorem total_source_native_frame_transform
    (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool)
    (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)
    (z : B.Domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    ConcreteApproximationGroupAction.CM.totalBallAmbientAction K g (AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val x) =
      AdaptedTotal.CM.totalNativePeriodFrame K B places d (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
        ((totalSourceFrameMatrix K g hdet B places d z.val).mulVec x) := by
  rw [total_source_frame_matrix_mulVec]
  funext j
  fin_cases j
  · exact SourceFrameAction.CM.source_native_frame_transform K g hdet B places (d 0) hg z (fun p => x (.inl p))
  · exact SourceFrameAction.CM.source_native_frame_transform K g hdet B places (d 1) hg z (fun p => x (.inr p))

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g)

theorem approximation_principal_native_ball_action (z : D.ball.Domain) :
    RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg) •
      SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z =
      SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1 z) :=
  SourceIntrinsicLine.CM.source_native_principal_ball_action K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid)
    D.ball.other_place N g hg z

theorem approximation_frame_coefficients_action (z : D.ball.Domain)
    (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    ConcreteApproximationFrameDeterminant.CM.approximationNativeFrameCoefficientEquiv K D A hid
      ((totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val).mulVec u) =
      (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).mulVec (ConcreteApproximationFrameDeterminant.CM.approximationNativeFrameCoefficientEquiv K D A hid u) := by
  let z' := BallLineAction.CM.ballPrincipalAction K D.ball g hg.1 z
  let S := totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val
  let w := AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u
  have hs := (ConcreteApproximationGroupAction.CM.total_ball_action_basis_commute K g A.basis w).trans
    (congrArg (ComplexTransition.CM.complexTensorBasisChange K A.basis)
      (total_source_native_frame_transform K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) hg.1 z u))
  have hc := (congrArg (ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid) hs).trans
    (ConcreteApproximationFrameDeterminant.CM.approximation_native_frame_coefficients K D A hid z' (S.mulVec u))
  have ha := ConcreteApproximationGroupAction.CM.approximation_complex_components_action K D A hid N g hg
    (ComplexTransition.CM.complexTensorBasisChange K A.basis w)
  have hf := congrArg (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)) (ConcreteApproximationFrameDeterminant.CM.approximation_native_frame_coefficients K D A hid z u)
  have hn := RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance.geometric_frame_covariance (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
    (ConcreteApproximationFrameDeterminant.CM.approximationNativeFrameCoefficientEquiv K D A hid u)
  have hb := congrArg (fun y => RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) y
    ((RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).mulVec (ConcreteApproximationFrameDeterminant.CM.approximationNativeFrameCoefficientEquiv K D A hid u)))
    (approximation_principal_native_ball_action K D A hid N g hg z)
  exact RepresentationTheory.Theta.Adelic.GeometricFrame.geometricFrame_injective (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z')
    (hc.symm.trans (ha.trans (hf.trans (hn.trans hb))))

def approximationIndexedFrameAction (z : D.ball.Domain) :
    Matrix (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places) ℂ :=
  (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
    (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).submatrix (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)

theorem approximation_frame_action_matrix (z : D.ball.Domain) :
    ConcreteApproximationFrameDeterminant.CM.approximationIndexedFrameCoefficientMatrix K D A hid *
      totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val =
      approximationIndexedFrameAction K D A hid N g hg z * ConcreteApproximationFrameDeterminant.CM.approximationIndexedFrameCoefficientMatrix K D A hid := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  simp only [← Matrix.mulVec_mulVec]
  have h := congrArg (fun x : Fin D.places.count × (Fin 3 × Fin 2) → ℂ =>
    fun i => x (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places i)) (approximation_frame_coefficients_action K D A hid N g hg z u)
  have hl := ConcreteApproximationFrameDeterminant.CM.approximation_indexed_frame_coefficient_apply K D A hid
    ((totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val).mulVec u)
  have hr := (congrArg (Matrix.mulVec (approximationIndexedFrameAction K D A hid N g hg z))
    (ConcreteApproximationFrameDeterminant.CM.approximation_indexed_frame_coefficient_apply K D A hid u)).trans
      (SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
        (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
          (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)) (ConcreteApproximationFrameDeterminant.CM.approximationNativeFrameCoefficientEquiv K D A hid u))
  exact hl.trans (h.trans hr.symm)

end

/-! The full split-source tensor transforms on the one common principal
level obtained for the original total finite input. This law is derived
from the native tensor and the actual frame action. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def sourceAdaptedThetaTensor {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (a : ℕ) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    ContinuousMultilinearMap ℂ (fun _ : Fin a => PeriodTotal.CM.TotalPositions K places → ℂ) ℂ :=
  (((L 0).halfDet z : ℂ) * ((L 1).halfDet z : ℂ)) •
    (iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z))) 0).compContinuousLinearMap
      (fun _ => (Matrix.toLin' (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z)ᵀ).toContinuousLinearMap)

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g)

theorem approximation_dual_frame_action (z : D.ball.Domain) (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid
      ((totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val)⁻¹ᵀ.mulVec u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid u) := by
  have h := congrArg (fun M : Matrix (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places) ℂ => M⁻¹ᵀ)
    (approximation_frame_action_matrix K D A hid N g hg z)
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at h
  have hv := congrArg (fun M => M.mulVec u) h
  simp only [← Matrix.mulVec_mulVec] at hv
  have hi := congrArg (fun x : PeriodTotal.CM.TotalPositions K D.places → ℂ =>
    fun j => x ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm j)) hv
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
    (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)) ((ConcreteApproximationFrameDeterminant.CM.approximationIndexedFrameCoefficientMatrix K D A hid)⁻¹ᵀ.mulVec u)
  exact hi.trans hr

omit N g hg in
theorem approximation_native_source_adapted_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z₀ z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (fun j => ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid (u j)) =
      (((Nat.factorial a : ℂ)⁻¹) * ConcreteApproximationFrameDeterminant.CM.approximationNativeHalfRatio K D A hid z₀) *
        sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) a z.val u := by
  have h := ConcreteApproximationGeometricTensor.CM.approximation_native_geometric_tensor K D A hid φ z₀ z a u
  simpa only [sourceAdaptedThetaTensor, _root_.smul_apply, smul_eq_mul,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, mul_assoc] using! h

theorem approximation_source_tensor_covariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (hcov : ConcreteApproximationLevel.CM.ActualApproximationThetaCovariant K D hid φ N g hg)
    (z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) a
      (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
      (fun j => (totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val)⁻¹ᵀ.mulVec (u j)) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 *
        sourceAdaptedThetaTensor K A.periods (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ) a z.val u := by
  let z' := BallLineAction.CM.ballPrincipalAction K D.ball g hg.1 z
  let S := totalSourceFrameMatrix K g hg.2.1 D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val
  let c := ((Nat.factorial a : ℂ)⁻¹) * ConcreteApproximationFrameDeterminant.CM.approximationNativeHalfRatio K D A hid z
  have hc : c ≠ 0 := mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)))
    (ConcreteApproximationFrameDeterminant.CM.approximation_native_half_ratio_ne_zero K D A hid z)
  have hu : (fun j => ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid (S⁻¹ᵀ.mulVec (u j))) =
      (fun j => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (ConcreteApproximationLevel.CM.setupArchimedeanElement K D N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid (u j))) :=
    funext (fun j => approximation_dual_frame_action K D A hid N g hg z (u j))
  have hl := approximation_native_source_adapted_tensor K D A hid φ z z' a (fun j => S⁻¹ᵀ.mulVec (u j))
  have hr := approximation_native_source_adapted_tensor K D A hid φ z z a u
  have he := congrArg (RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ) a
    (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z')) hu
  have hn := hcov ε A z a (fun j => ConcreteApproximationGeometricTensor.CM.approximationNativeDualCoordinates K D A hid (u j))
  have ht := congrArg (fun x : ℂ => ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 * x) hr
  apply mul_left_cancel₀ hc
  exact (hl.symm.trans (he.trans (hn.trans ht))).trans (mul_left_comm _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction.CM
