import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonJets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedInverseMultiplier

/-! # Comparison Return Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonReturnTensor.CM

noncomputable section

section

/-! Return an arbitrary native factor input through its actual rational
source transition. The forward-and-return completed theta series differ
by the exact inverse-oscillator scalar, at every Jacobi argument. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W}
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A)
  {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)

def comparisonIndexedSourceInput
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I :=
  (ReindexTheta.CM.finiteInputReindex e).symm (Comparison.CM.comparisonSourceInput C f)

omit [DecidableEq I] in
theorem comparison_source_reindexed_completed_theta
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f Z.matrix ξ =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (comparisonIndexedSourceInput C e f) (ReindexTheta.CM.siegelReindex e.symm Z)
        (fun i => ξ (e i)) := by
  rw [Comparison.CM.comparison_source_completed_theta]
  have h := SourceIntrinsicComparison.CM.completed_reindex_from_target e (comparisonIndexedSourceInput C e f) Z
    (fun i => ξ (e i))
  change RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (ReindexTheta.CM.finiteInputReindex e ((ReindexTheta.CM.finiteInputReindex e).symm _)) Z _ = _ at h
  simpa only [Equiv.apply_symm_apply] using h

def comparisonReturnInput (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input I :=
  IndexedCovariance.CM.indexedFiniteOscillatorInput γ⁻¹ (comparisonIndexedSourceInput C e f)

theorem comparison_return_completed_theta (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (U : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (hU : ReindexTheta.CM.siegelReindex e.symm U = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
    (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C (Comparison.CM.comparisonFiniteInput C
      (ReindexTheta.CM.finiteInputReindex e (IndexedCovariance.CM.indexedFiniteOscillatorInput γ (comparisonReturnInput C e γ f))))
      U.matrix ξ = IndexedInverseMultiplier.CM.indexedInverseMultiplier γ Z * RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f U.matrix ξ := by
  rw [Comparison.CM.comparison_input_completed_theta, comparison_source_reindexed_completed_theta C e f]
  have he := SourceIntrinsicComparison.CM.completed_reindex_from_target e
    (IndexedCovariance.CM.indexedFiniteOscillatorInput γ (comparisonReturnInput C e γ f)) U (fun i => ξ (e i))
  simp only [Equiv.apply_symm_apply] at he
  rw [he, hU]
  exact IndexedInverseMultiplier.CM.indexed_inverse_oscillator_completed γ (comparisonIndexedSourceInput C e f) Z _

end

/-! The native finite-input return identity holds for every completed
Taylor coefficient and the full geometric tensor, with its factorial
and half-frame normalizations unchanged. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.BallNatural

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W}
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A)
  {I : Type} [Fintype I] [DecidableEq I] (e : I ≃ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)

theorem comparison_return_completed_theta_jets (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (U : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (hU : ReindexTheta.CM.siegelReindex e.symm U = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
    (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C (Comparison.CM.comparisonFiniteInput C
      (ReindexTheta.CM.finiteInputReindex e (IndexedCovariance.CM.indexedFiniteOscillatorInput γ (comparisonReturnInput C e γ f))))
      U.matrix) 0 u = IndexedInverseMultiplier.CM.indexedInverseMultiplier γ Z *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f U.matrix) 0 u := by
  have he : RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C (Comparison.CM.comparisonFiniteInput C
      (ReindexTheta.CM.finiteInputReindex e (IndexedCovariance.CM.indexedFiniteOscillatorInput γ (comparisonReturnInput C e γ f))))
      U.matrix = IndexedInverseMultiplier.CM.indexedInverseMultiplier γ Z • RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f U.matrix :=
    funext (fun ξ => comparison_return_completed_theta C e γ f Z U hU ξ)
  have hg : ContDiffAt ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f U.matrix) 0 := by
    have hf : RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f U.matrix = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (Comparison.CM.comparisonSourceInput C f) U :=
      funext (fun ξ => Comparison.CM.comparison_source_completed_theta C f U ξ)
    rw [hf]
    exact ((RepresentationTheory.Theta.Kernel.Analysis.adelic_analysis (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) _ U).2.of_le (by simp)).contDiffAt
  have h := congrArg (fun g => iteratedFDeriv ℂ a g 0 u) he
  rw [iteratedFDeriv_const_smul_apply hg] at h
  exact h

theorem comparison_return_geometric_tensor (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ)
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (hZ : ReindexTheta.CM.siegelReindex e.symm (C.period z) = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z)
    (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor C (Comparison.CM.comparisonFiniteInput C
      (ReindexTheta.CM.finiteInputReindex e (IndexedCovariance.CM.indexedFiniteOscillatorInput γ (comparisonReturnInput C e γ f))))
      a z u = IndexedInverseMultiplier.CM.indexedInverseMultiplier γ Z * RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor C f a z u := by
  have h := comparison_return_completed_theta_jets C e γ f Z (C.period z) hZ a
    (fun k => (C.frame z).invᵀ.mulVec (u k))
  have hs := congrArg (fun t : ℂ => (C.halfFrame z)⁻¹ * ((Nat.factorial a : ℂ)⁻¹ * t)) h
  exact hs.trans (by
    change _ = IndexedInverseMultiplier.CM.indexedInverseMultiplier γ Z * ((C.halfFrame z)⁻¹ *
      ((Nat.factorial a : ℂ)⁻¹ * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f (C.period z).matrix) 0
        (fun k => (C.frame z).invᵀ.mulVec (u k))))
    ring)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonReturnTensor.CM
