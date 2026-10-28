import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSum
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonJets

/-! # Intrinsic Kernel Sum Jets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumJets.CM

noncomputable section

/-! All Taylor tensors of the retained source input agree with the
native tensors through the exact Jacobi coordinate map. No projection
or selected Taylor coefficient is used in this comparison. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include hG in
theorem sum_comparison_completed_theta_jets
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (a : ℕ)
    (v : Fin a → PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta N
        (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ)
        (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) 0
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
  let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
  let Ψ := IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ
  let W := N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  let v' := fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i)
  have hn := ComparisonJets.CM.comparison_input_completed_theta_jets N (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) Ψ) W a
    (fun i j => v' i ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j))
  have hr := SourceIntrinsicComparison.CM.reindexed_completed_theta_jets (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) Ψ W a v'
  have hp := congrArg (fun U => iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ U) 0 v')
    (IntrinsicKernelSumPeriod.CM.sum_comparison_period_transform K d Q hμ N hN hG L hL z)
  have hi := IndexedCovariance.CM.indexed_completed_jet_covariance γ φ Z a v
  exact hn.trans (hr.trans (hp.trans hi))

include hG in
theorem sum_comparison_completed_tensor
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z₀ z : B.Domain) (a : ℕ)
    (v : Fin a → PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor N
      (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ) a
      (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j)) =
      ((Nat.factorial a : ℂ)⁻¹) *
        (KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
          (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
            (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)))) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  dsimp only
  have ht := sum_comparison_completed_theta_jets K d Q hμ N hN hG L hL φ z a v
  have hm := IntrinsicKernelSum.CM.sum_comparison_multiplier_factor K d Q hμ N hN hG L hL z₀ z
  have he := ht.trans (congrArg (fun c => c * iteratedFDeriv ℂ a
    (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val))) 0 v) hm)
  have h := congrArg (fun c : ℂ => ((Nat.factorial a : ℂ)⁻¹) * c) he
  simpa only [RepresentationTheory.Theta.Adelic.DataTheta.completedTensor, _root_.smul_apply, smul_eq_mul, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumJets.CM
