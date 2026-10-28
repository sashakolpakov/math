import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussianCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalModel

/-! # Classical Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalCovariance.CM

noncomputable section

/-! ThetaCycle: exact classical and completed theta covariance for every
supplied finite Schwartz input, using the actual rational oscillator. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

theorem rational_theta_archimedean_scalar (N : ℕ) (φ ψ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests ℚ N) (c : ℂ)
    (h : ∀ v, ψ v = c • φ v) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N) : RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta ℚ N ψ f = c * RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta ℚ N φ f := by
  have hv (q : Fin N → ℚ) : RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N ψ q = c * RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N φ q := by
    unfold RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue
    rw [Fintype.prod_unique, Fintype.prod_unique, h]
    rfl
  change (∑' q, RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N ψ q * RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction ℚ N f
      (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q)) = c * ∑' q, RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N φ q *
        RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction ℚ N f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q)
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [hv, mul_assoc]

def classicalFiniteOscillatorInput (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N) :=
  ClassicalModel.CM.rationalOscillatorFiniteInput N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) φ

theorem classical_theta_oscillator_covariance (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    (RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z * Complex.exp (-(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z z z)) *
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (classicalFiniteOscillatorInput N γ φ)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z.matrix z := by
  have h := ClassicalModel.CM.original_input_oscillator_theta N (OscillatorPhaseOrder.CM.swapSymplecticPhase γ) φ Z z
  rw [rational_theta_archimedean_scalar N _ _ _ (RationalGaussianCovariance.CM.rational_archimedean_gaussian_action N γ Z z),
    ClassicalModel.CM.native_theta_classical_series] at h
  exact h

theorem completion_gaussian_correction {N : ℕ} (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (Fin N) ℝ)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * Complex.exp (-g.thetaCorrectionForm Z z z) =
      ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (g.transformSiegel Z).completionForm (g.jacobiChange Z z) := by
  rw [ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, ← Complex.exp_add]
  congr 1
  have h := g.completion_correction_identity Z z
  linear_combination -h

theorem completed_theta_oscillator_covariance (N : ℕ) (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp (Fin N) ℚ)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z *
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (classicalFiniteOscillatorInput N γ φ)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z z := by
  have h := congrArg (fun t => ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * t)
    (classical_theta_oscillator_covariance N γ φ Z z)
  unfold RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed
  calc
    _ = (ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor Z.completionForm z * Complex.exp (-(RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).thetaCorrectionForm Z z z)) *
        (RationalGaussianCovariance.CM.rationalGaussianCoefficient N γ Z *
          RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (classicalFiniteOscillatorInput N γ φ)
            ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z z)) := by
      rw [completion_gaussian_correction]
      ring
    _ = _ := by convert h using 1; ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalCovariance.CM
