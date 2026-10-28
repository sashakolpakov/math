import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicHalfRatio
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference

/-! # Source Intrinsic Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison.CM

noncomputable section

section

/-! The original finite Schwartz input is transported once through the
fixed rational coordinate change. The resulting native completed theta
series agrees with the original source series throughout the ball, with
its exact constant and geometric half-frame factors. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem siegel_reindex_inverse {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) : ReindexTheta.CM.siegelReindex e (ReindexTheta.CM.siegelReindex e.symm Z) = Z := by
  apply ReindexTheta.CM.siegel_matrix_ext
  ext i j
  simp only [ReindexTheta.CM.siegelReindex, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    Equiv.apply_symm_apply]

theorem completed_reindex_from_target {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) (ξ : I → ℂ) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ReindexTheta.CM.finiteInputReindex e φ) Z (fun j => ξ (e.symm j)) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (ReindexTheta.CM.siegelReindex e.symm Z) ξ := by
  have h := ReindexTheta.CM.completed_reindex e φ (ReindexTheta.CM.siegelReindex e.symm Z) ξ
  simpa only [siegel_reindex_inverse] using h

section FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (C : Fin 2 → HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (hC : ∀ j, (C j).a = Q.a j ∧ (C j).delta = Q.delta)

def directSourceNativeFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 2) :=
  IntrinsicReference.CM.nativeOriginalFiniteInput (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother C hC) φ))

end FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

theorem source_native_multiplier_factor (z₀ z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) =
      SourceIntrinsicHalfRatio.CM.sourceNativeHalfRatio K d Q hμ hother L hL z₀ *
        ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) := by
  have he := div_mul_cancel₀
    (IndexedCovariance.CM.indexedThetaMultiplier (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)))
    (SourceIntrinsicHalfRatio.CM.source_native_half_denominator_ne_zero K d Q hμ hother L z)
  exact he.symm.trans (congrArg (fun c : ℂ => c *
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))))
    (SourceIntrinsicHalfRatio.CM.source_native_half_ratio_constant K d Q hμ hother L hL z₀ z))

theorem source_native_indexed_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ) (SourceIntrinsicPeriodGraph.CM.directSourceIndexedPeriod K Q hμ hother z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (congrArg (fun W => RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL) φ) W
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).jacobiChange
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ))
    (SourceIntrinsicPeriodGraph.CM.source_native_period_transform K d Q hμ hother L hL z)).trans
    (IndexedCovariance.CM.indexed_completed_theta_covariance _ φ _ ξ)

theorem source_native_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SourceComponents.CM.directSourceComparison K Q hμ hother)
      (directSourceNativeFiniteInput K Q hμ hother (fun j => (L j).coordinates) hL φ)
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  have hn := IntrinsicReference.CM.native_original_completed_theta (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (SourceComponents.CM.directSourceFrames K Q)
    (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
        (fun j => (L j).coordinates) hL) φ))
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).jacobiChange
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i))
  have he := completed_reindex_from_target (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL) φ)
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).jacobiChange
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ)
  exact hn.trans (he.trans (source_native_indexed_completed_theta K d Q hμ hother L hL φ z ξ))

theorem source_native_completed_theta_normalized
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z₀ z : B.Domain) (ξ : PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SourceComponents.CM.directSourceComparison K Q hμ hother)
      (directSourceNativeFiniteInput K Q hμ hother (fun j => (L j).coordinates) hL φ)
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i)) =
      SourceIntrinsicHalfRatio.CM.sourceNativeHalfRatio K d Q hμ hother L hL z₀ *
        ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (source_native_completed_theta K d Q hμ hother L hL φ z ξ).trans
    (congrArg (fun c => c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ξ)
      (source_native_multiplier_factor K d Q hμ hother L hL z₀ z))

end

/-! All Taylor tensors of the retained source input agree with the
native tensors through the exact Jacobi coordinate map. No projection
or selected Taylor coefficient is used in this comparison. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem reindexed_completed_theta_jets {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix J) (a : ℕ) (v : Fin a → I → ℂ) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ReindexTheta.CM.finiteInputReindex e φ) Z) 0
      (fun i j => v i (e.symm j)) =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (ReindexTheta.CM.siegelReindex e.symm Z)) 0 v := by
  let T := (LinearEquiv.funCongrLeft ℂ ℂ e.symm).toContinuousLinearEquiv.toContinuousLinearMap
  have hf : ContDiff ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ReindexTheta.CM.finiteInputReindex e φ) Z) :=
    (RepresentationTheory.Theta.Kernel.Analysis.adelic_analysis (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) _ Z).2.of_le (by simp)
  have he : (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ReindexTheta.CM.finiteInputReindex e φ) Z) ∘ T =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (ReindexTheta.CM.siegelReindex e.symm Z) :=
    funext (fun ξ => completed_reindex_from_target e φ Z ξ)
  have hd := congrArg (fun f => iteratedFDeriv ℂ a f 0 v) he
  rw [T.iteratedFDeriv_comp_right hf 0 le_rfl] at hd
  simpa only [map_zero, ContinuousMultilinearMap.compContinuousLinearMap_apply] using! hd

theorem native_original_completed_theta_jets
    {F : Type} [Field F] [NumberField F] {δ : F} {m : ℕ}
    {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F δ))ˣ}
    {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F δ))ˣ}
    (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F δ m H W) (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F δ 3 m H W)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (a : ℕ)
    (v : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison A P)
      (IntrinsicReference.CM.nativeOriginalFiniteInput A φ) Z.matrix) 0 v =
      iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v :=
  congrArg (fun f => iteratedFDeriv ℂ a f 0 v)
    (funext (fun ξ => IntrinsicReference.CM.native_original_completed_theta A P φ Z ξ))

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

theorem source_native_completed_theta_jets
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z : B.Domain) (a : ℕ)
    (v : Fin a → PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SourceComponents.CM.directSourceComparison K Q hμ hother)
        (directSourceNativeFiniteInput K Q hμ hother (fun j => (L j).coordinates) hL φ)
        ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) 0
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
  let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
  let Ψ := IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ
  let W := (SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  let v' := fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i)
  have hn := native_original_completed_theta_jets (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (SourceComponents.CM.directSourceFrames K Q) (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) Ψ) W a
    (fun i j => v' i ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j))
  have hr := reindexed_completed_theta_jets (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) Ψ W a v'
  have hp := congrArg (fun U => iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ U) 0 v')
    (SourceIntrinsicPeriodGraph.CM.source_native_period_transform K d Q hμ hother L hL z)
  have hi := IndexedCovariance.CM.indexed_completed_jet_covariance γ φ Z a v
  exact hn.trans (hr.trans (hp.trans hi))

theorem source_native_completed_tensor
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) (z₀ z : B.Domain) (a : ℕ)
    (v : Fin a → PeriodTotal.CM.TotalPositions K places → ℂ) :
    let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
    let Z := BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor (SourceComponents.CM.directSourceComparison K Q hμ hother)
      (directSourceNativeFiniteInput K Q hμ hother (fun j => (L j).coordinates) hL φ) a
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm j)) =
      ((Nat.factorial a : ℂ)⁻¹) *
        (SourceIntrinsicHalfRatio.CM.sourceNativeHalfRatio K d Q hμ hother L hL z₀ *
          ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
            (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)))) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  dsimp only
  have ht := source_native_completed_theta_jets K d Q hμ hother L hL φ z a v
  have hm := source_native_multiplier_factor K d Q hμ hother L hL z₀ z
  have he := ht.trans (congrArg (fun c => c * iteratedFDeriv ℂ a
    (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val))) 0 v) hm)
  have h := congrArg (fun c : ℂ => ((Nat.factorial a : ℂ)⁻¹) * c) he
  simpa only [RepresentationTheory.Theta.Adelic.DataTheta.completedTensor, _root_.smul_apply, smul_eq_mul, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison.CM
