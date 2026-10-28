import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalGaussian
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalSchwartzTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.FiniteCoverOperator

/-! # Classical Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalModel.CM

noncomputable section

/-! ThetaCycle: exact identification of the classical rational theta series with
the native adelic theta functional, retaining the supplied finite input. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation

def rationalSchwartzOfTensor (N : ℕ) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N) :=
  (RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N).symm (RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz ℚ N f)

theorem rational_schwartz_of_tensor_principal (N : ℕ) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N) (q : Fin N → ℚ) :
    (rationalSchwartzOfTensor N f).val (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal q) =
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction ℚ N f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q) := by
  have he : RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N (rationalSchwartzOfTensor N f) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz ℚ N f := (RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N).apply_symm_apply _
  have h := congrArg (fun g : RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions ℚ N => g.val (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q)) he
  exact (RationalSchwartzCoordinates.CM.rational_schwartz_to_adelic_principal N (rationalSchwartzOfTensor N f) q).symm.trans h

theorem native_theta_classical_series (N : ℕ) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz ℚ N)
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta ℚ N (RationalGaussian.CM.rationalArchimedeanGaussian N Z z) f =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (rationalSchwartzOfTensor N f) Z.matrix z := by
  apply tsum_congr
  intro q
  change RepresentationTheory.Theta.Adelic.ThetaEvaluation.archimedeanValue ℚ N (RationalGaussian.CM.rationalArchimedeanGaussian N Z z) q *
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction ℚ N f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition q) = _
  rw [RationalGaussian.CM.rational_gaussian_archimedean_value, ← rational_schwartz_of_tensor_principal]
  exact mul_comm _ _

theorem rational_schwartz_tensor_roundtrip (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) :
    rationalSchwartzOfTensor N (RationalSchwartzTensor.CM.rationalSchwartzTensor N φ) = φ := by
  apply (RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N).injective
  exact (RationalSchwartzCoordinates.CM.rationalSchwartzToAdelicFunctions N).apply_symm_apply _ |>.trans
    (RationalSchwartzTensor.CM.rational_schwartz_tensor_function N φ)

theorem native_theta_original_input (N : ℕ) (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta ℚ N (RationalGaussian.CM.rationalArchimedeanGaussian N Z z) (RationalSchwartzTensor.CM.rationalSchwartzTensor N φ) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z.matrix z := by
  rw [native_theta_classical_series, rational_schwartz_tensor_roundtrip]

def rationalOscillatorFiniteInput (N : ℕ) (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ N)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N) :=
  rationalSchwartzOfTensor N (FiniteCoverOperator.CM.finiteCoverOperator ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ)
    (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N γ) (RationalSchwartzTensor.CM.rationalSchwartzTensor N φ))

theorem original_input_oscillator_theta (N : ℕ) (γ : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Symplectic ℚ N)
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin N)) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (Fin N)) (z : Fin N → ℂ) :
    RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta ℚ N (FiniteCoverOperator.CM.archimedeanCoverOperator ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ)
        (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N γ) (RationalGaussian.CM.rationalArchimedeanGaussian N Z z))
      (FiniteCoverOperator.CM.finiteCoverOperator ℚ N (FieldAdelicCharacter.CM.fieldAdelicCharacter ℚ)
        (RationalOscillator.CM.restrictedFieldRationalOscillator ℚ N γ) (RationalSchwartzTensor.CM.rationalSchwartzTensor N φ)) =
      RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z.matrix z :=
  (FiniteCoverOperator.CM.rational_tensor_theta_covariance ℚ N γ _ _).trans (native_theta_original_input N φ Z z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ClassicalModel.CM
