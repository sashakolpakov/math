import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameDeterminant

/-! # Concrete Approximation Normalized -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationNormalized.CM

noncomputable section

/-! All completed split-source Taylor tensors are the tensors of the
one fixed native input, with their actual constant normalization. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem rational_jacobi_left_inverse {I : Type} [Fintype I] [DecidableEq I]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (u : I → ℂ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ⁻¹).jacobiChange ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z u) = u := by
  rw [InverseSiegelAction.CM.rational_inverse_jacobi_action, ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply,
    Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.nonsing_inv_mul _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).denominator_det_isUnit Z),
    Matrix.transpose_one, Matrix.one_mulVec]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def approximationNativeJacobi (z : HeckeCycles.GeometricSource.CM.BallChart) (u : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    Fin D.places.count × (Fin 3 × Fin 2) → ℂ :=
  fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)).jacobiChange
    (MovingTotalPeriod.CM.approximationTotalPeriod K D A z)
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).jacobiChange
      (BlockPeriod.CM.blockPeriod ((A.periods 0).period z) ((A.periods 1).period z)) u)
    ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i)

theorem approximation_split_native_theta_jets (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ)
        ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).matrix) 0
      (fun j => approximationNativeJacobi K D A hid z.val (u j)) =
      (IndexedCovariance.CM.indexedThetaMultiplier (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
        (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z.val) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
          (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val))) 0 u := by
  let Z := BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val)
  let u' := fun j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (PeriodTotal.CM.approximationSymplecticMatrix K D A)).jacobiChange Z (u j)
  have hn := ConcreteApproximationComparison.CM.approximation_original_completed_theta_jets K D A hid φ z a u'
  have hs := ApproximationCovariance.CM.approximation_completed_jet_covariance K D A φ z.val a u'
  have hu : (fun j => ApproximationCovariance.CM.approximationJacobiPullback K D A z.val (u' j)) = u :=
    funext (fun j => rational_jacobi_left_inverse (PeriodTotal.CM.approximationSymplecticMatrix K D A) Z (u j))
  rw [hu] at hs
  have he := congrArg (fun c : ℂ =>
    (IndexedCovariance.CM.indexedThetaMultiplier (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid)
      (MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val) / ApproximationCovariance.CM.approximationThetaMultiplier K D A z.val) * c) hs
  rw [← mul_assoc, div_mul_cancel₀ _ (ApproximationCovariance.CM.approximation_theta_multiplier_ne_zero K D A z.val)] at he
  exact hn.trans he.symm

theorem approximation_split_native_completed_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z₀ z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ) a
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).matrix
      (fun j => approximationNativeJacobi K D A hid z.val (u j)) =
      ((Nat.factorial a : ℂ)⁻¹) *
        (ConcreteApproximationFrameDeterminant.CM.approximationNativeHalfRatio K D A hid z₀ *
          ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) *
            (((A.periods 0).halfDet z.val : ℂ) * ((A.periods 1).halfDet z.val : ℂ)))) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
          (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val))) 0 u := by
  have ht := approximation_split_native_theta_jets K D A hid φ z a u
  have hm := ConcreteApproximationFrameDeterminant.CM.approximation_native_multiplier_factor K D A hid z₀ z
  have he := ht.trans (congrArg (fun c => c * iteratedFDeriv ℂ a
    (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ApproximationCovariance.CM.approximationSplitFiniteInput K D A φ)
      (BlockPeriod.CM.blockPeriod ((A.periods 0).period z.val) ((A.periods 1).period z.val))) 0 u) hm)
  have h := congrArg (fun c : ℂ => ((Nat.factorial a : ℂ)⁻¹) * c) he
  simpa only [RepresentationTheory.Theta.Adelic.DataTheta.completedTensor, _root_.smul_apply, smul_eq_mul, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationNormalized.CM
