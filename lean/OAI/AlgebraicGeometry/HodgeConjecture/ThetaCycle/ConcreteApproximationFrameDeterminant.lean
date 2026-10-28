import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationPeriodGraph
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ApproximationCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicHalfRatio

/-! # Concrete Approximation Frame Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameDeterminant.CM

noncomputable section

section

/-! The two actual symplectic denominators factor through the native
frame, one constant invertible coefficient map, and the split source
adapted frame. This determines the normalization without changing the
original finite input. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem frame_product_determinant {I : Type} [Fintype I] [DecidableEq I]
    (J₀ J F C G : Matrix I I ℂ) (a b : ℂ)
    (h : J₀ * J = F * C * G) (hF : F.det = a ^ 2) (hG : G.det = b ^ 2) :
    J₀.det * J.det = (a * b) ^ 2 * C.det := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, hF, hG] at hd
  exact hd.trans (by ring)

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationNativeFrameCoefficientEquiv :
    (PeriodTotal.CM.TotalPositions K D.places → ℂ) ≃ₗ[ℂ] (Fin D.places.count × (Fin 3 × Fin 2) → ℂ) :=
  (ConcreteApproximationGeometricFrame.CM.exists_actual_approximation_geometric_frame K D A hid).choose

theorem approximation_native_frame_coefficients (z : D.ball.Domain)
    (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid (ComplexTransition.CM.complexTensorBasisChange K A.basis
      (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u)) =
    RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
      (approximationNativeFrameCoefficientEquiv K D A hid u) :=
  (ConcreteApproximationGeometricFrame.CM.exists_actual_approximation_geometric_frame K D A hid).choose_spec z u

def approximationIndexedFrameCoefficientEquiv :
    (PeriodTotal.CM.TotalPositions K D.places → ℂ) ≃ₗ[ℂ] (PeriodTotal.CM.TotalPositions K D.places → ℂ) :=
  (approximationNativeFrameCoefficientEquiv K D A hid).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places))

def approximationIndexedFrameCoefficientMatrix :
    Matrix (PeriodTotal.CM.TotalPositions K D.places) (PeriodTotal.CM.TotalPositions K D.places) ℂ :=
  LinearMap.toMatrix' (approximationIndexedFrameCoefficientEquiv K D A hid).toLinearMap

theorem approximation_indexed_frame_coefficient_apply (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    (approximationIndexedFrameCoefficientMatrix K D A hid).mulVec u =
      fun i => approximationNativeFrameCoefficientEquiv K D A hid u (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places i) := by
  rw [approximationIndexedFrameCoefficientMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem approximation_indexed_frame_coefficient_det_ne_zero :
    (approximationIndexedFrameCoefficientMatrix K D A hid).det ≠ 0 := by
  rw [approximationIndexedFrameCoefficientMatrix, LinearMap.det_toMatrix']
  exact (approximationIndexedFrameCoefficientEquiv K D A hid).isUnit_det'.ne_zero

theorem approximation_native_indexed_frame_det (z : D.ball.Domain) :
    (IntrinsicIndexedGraphs.CM.nativeIndexedFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
      (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).det =
      (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) ^ 2 := by
  dsimp only [ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison]
  have hh := @IntrinsicIndexedGraphs.CM.native_indexed_frame_det (maximalRealSubfield K) _ (BallArithmetic.CM.directNativeRealNumberField K)
    (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D)) 2
    (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) D.ball.b (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_fixed K D)
      (ConcreteApproximationIntrinsicArithmetic.CM.setup_ball_nonzero K D))
    (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_imaginary K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_delta_ne_zero K D) D.pair.a
      (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_fixed K D) (ConcreteApproximationIntrinsicArithmetic.CM.setup_a_nonzero K D))
    (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
    (PeriodTotal.CM.TotalPositions K D.places) _ (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) _ (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
  dsimp only [IntrinsicIndexedGraphs.CM.nativeIndexedFrame, ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison] at hh ⊢
  exact hh

theorem approximation_native_frame_denominator_apply (z : D.ball.Domain)
    (x : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)
    let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator Z.matrix
    let J₀ := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)).complexify.denominator
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val).matrix
    J₀.mulVec (J.mulVec x) =
      (IntrinsicIndexedGraphs.CM.nativeIndexedFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
        (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).mulVec
        ((approximationIndexedFrameCoefficientMatrix K D A hid).mulVec
          ((SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val).mulVec x)) := by
  let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator Z.matrix
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (D.initialPeriods j).coordinates)
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) (J.mulVec x)
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K D.places (FourSplittings.CM.newThetaSigns K v)
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (A.periods j).coordinates) Z x)
  have hr : ComplexTransition.CM.complexTensorBasisChange K A.basis
      (AdaptedTotal.CM.totalNativePeriodFrame K D.ball D.places (FourSplittings.CM.newThetaSigns K v) z.val u) = w :=
    (congrArg (ComplexTransition.CM.complexTensorBasisChange K A.basis)
      (AdaptedTotal.CM.total_native_frame_recovers_graph K A.periods z.val z.property x)).trans
        (MovingTotalPeriod.CM.approximation_total_graph K D A z.val x).symm
  have hf := (congrArg (ConcreteApproximationComplexComponents.CM.approximationComplexComponents K D A hid) hr).symm.trans
    (approximation_native_frame_coefficients K D A hid z u)
  have ht := (ConcreteApproximationComplexComponents.CM.approximation_original_complex_transition K D A hid w).trans hf
  let γ := ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid
  have hp := IntrinsicIndexedGraphs.CM.native_indexed_graph_bottom (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (SourceComponents.CM.directSourceFrames K D.pair) (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
    (γ.val.map (algebraMap ℚ ℂ) *ᵥ ComplexTransition.CM.totalComplexCoordinates K (fun j => (D.initialPeriods j).coordinates) w)
    (approximationNativeFrameCoefficientEquiv K D A hid u) ht
  have hc := congrArg (fun y => γ.val.map (algebraMap ℚ ℂ) *ᵥ y)
    (TotalPeriodGraphs.CM.total_graph_coordinates K (fun j => (D.initialPeriods j).coordinates)
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) (J.mulVec x))
  have hα := hc.trans (MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) (J.mulVec x))
  have hb := congrArg (fun y : (PeriodTotal.CM.TotalPositions K D.places ⊕ PeriodTotal.CM.TotalPositions K D.places) → ℂ =>
    fun i => y (.inr i)) hα
  have hbottom := hb.symm.trans hp
  have hi := SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
    ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).val
    (approximationNativeFrameCoefficientEquiv K D A hid u)
  have ho := congrArg (Matrix.mulVec
    (IntrinsicIndexedGraphs.CM.nativeIndexedFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
      (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)))
    (approximation_indexed_frame_coefficient_apply K D A hid u)
  have he := hbottom.trans (ho.trans hi).symm
  simpa only [SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_apply] using! he

theorem approximation_native_frame_denominator_matrix (z : D.ball.Domain) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)).complexify.denominator
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val).matrix *
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)).matrix =
      IntrinsicIndexedGraphs.CM.nativeIndexedFrame (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
        (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
        approximationIndexedFrameCoefficientMatrix K D A hid * SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K A.periods z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec]
  exact approximation_native_frame_denominator_apply K D A hid z x

theorem approximation_native_frame_denominator_det (z : D.ball.Domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)).complexify.denominator
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val).matrix).det *
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)).matrix).det =
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
        (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ))) ^ 2 *
          (approximationIndexedFrameCoefficientMatrix K D A hid).det := by
  exact frame_product_determinant _ _ _ _ _ _ _
    (approximation_native_frame_denominator_matrix K D A hid z)
    (approximation_native_indexed_frame_det K D A hid z)
    (SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_det K A.periods z)

theorem approximation_native_multiplier_ratio_square (z : D.ball.Domain) :
    (IndexedCovariance.CM.indexedThetaMultiplier (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z.val) ^ 2 =
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
        (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ))) ^ 2 *
          (approximationIndexedFrameCoefficientMatrix K D A hid).det := by
  rw [div_pow, IndexedCovariance.CM.indexed_theta_multiplier_square, ApproximationCovariance.CM.approximation_theta_multiplier_square, div_inv_eq_mul]
  exact approximation_native_frame_denominator_det K D A hid z

end

/-! Every actual approximation has a nonzero constant normalization
between its split source half-frames and its native half-frame. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.ContinuousSquareRoot

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationNativeHalfRatio (z : D.ball.Domain) : ℂ :=
  (IndexedCovariance.CM.indexedThetaMultiplier (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z.val) /
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
        (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ)))

theorem approximation_native_half_denominator_ne_zero (z : D.ball.Domain) :
    (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
      (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ)) ≠ 0 :=
  mul_ne_zero (((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (SourceComponents.CM.directSourceFrames K D.pair)).2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).1)
    (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))

theorem approximation_native_half_ratio_ne_zero (z : D.ball.Domain) :
    approximationNativeHalfRatio K D A hid z ≠ 0 :=
  div_ne_zero (div_ne_zero (IndexedCovariance.CM.indexed_theta_multiplier_ne_zero _ _)
    (ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z.val))
    (approximation_native_half_denominator_ne_zero K D A hid z)

theorem approximation_native_half_ratio_square (z : D.ball.Domain) :
    approximationNativeHalfRatio K D A hid z ^ 2 =
      (approximationIndexedFrameCoefficientMatrix K D A hid).det := by
  unfold approximationNativeHalfRatio
  rw [div_pow]
  apply (div_eq_iff (pow_ne_zero 2 (approximation_native_half_denominator_ne_zero K D A hid z))).mpr
  exact (approximation_native_multiplier_ratio_square K D A hid z).trans (mul_comm _ _)

theorem approximation_native_half_ratio_continuous :
    Continuous (approximationNativeHalfRatio K D A hid) := by
  have : Nonempty (PeriodTotal.CM.TotalPositions K D.places) := ⟨.inl (D.places.distinguished, 0)⟩
  have hZ := MovingTotalPeriod.CM.approximation_total_period_holomorphic K D A
  have hm := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A) hZ).continuousOn.domRestrict
  have ha := (IndexedCovariance.CM.indexed_theta_multiplier_holomorphic (PeriodTotal.CM.approximationSymplecticMatrix K D A)⁻¹
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A) hZ).continuousOn.domRestrict
  have hn := (RepresentationTheory.Theta.Adelic.BallHolomorphicSquare.ball_holomorphic_continuous _
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
      (SourceComponents.CM.directSourceFrames K D.pair)).2.2.2.2.1).comp (SourceIntrinsicBall.CM.source_native_ball_continuous K D.ball)
  have hs₀ := (A.periods 0).halfDet_holomorphic.continuousOn.domRestrict
  have hs₁ := (A.periods 1).halfDet_holomorphic.continuousOn.domRestrict
  exact (hm.div ha (fun z => ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z.val)).div
    (hn.mul (hs₀.mul hs₁)) (approximation_native_half_denominator_ne_zero K D A hid)

theorem approximation_native_half_ratio_constant (z₀ z : D.ball.Domain) :
    approximationNativeHalfRatio K D A hid z = approximationNativeHalfRatio K D A hid z₀ := by
  have : ConnectedSpace D.ball.Domain := BallConnected.CM.ball_domain_connected D.ball
  have h := RepresentationTheory.Theta.Adelic.ContinuousSquareRoot.continuous_square_roots_eq (approximationNativeHalfRatio K D A hid)
    (fun _ => approximationNativeHalfRatio K D A hid z₀)
    (approximation_native_half_ratio_continuous K D A hid) continuous_const
    (approximation_native_half_ratio_ne_zero K D A hid)
    (fun y => (approximation_native_half_ratio_square K D A hid y).trans
      (approximation_native_half_ratio_square K D A hid z₀).symm) z₀ rfl
  exact congrFun h z

theorem approximation_native_multiplier_factor (z₀ z : D.ball.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z.val =
      approximationNativeHalfRatio K D A hid z₀ *
        ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
          (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ))) := by
  rw [← approximation_native_half_ratio_constant K D A hid z₀ z]
  exact (div_mul_cancel₀ _ (approximation_native_half_denominator_ne_zero K D A hid z)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameDeterminant.CM
