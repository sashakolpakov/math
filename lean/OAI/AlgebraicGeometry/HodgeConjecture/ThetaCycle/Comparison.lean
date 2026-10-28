import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFiniteTestReturn
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference

/-! # Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Comparison.CM

noncomputable section

/-! Exact completed theta identities in both directions for any native
comparison coordinates. The finite inputs are fixed functions, and every
rational weight is preserved. -/

open scoped Classical _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
  {H : (Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
  {A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData F d m H W}
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData F H W A)

def comparisonFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m) :=
  FieldFinite.CM.sourceFieldFiniteInput A (Equiv.refl _) C.rationalPosition φ

theorem comparison_input_rational_theta (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta C (comparisonFiniteInput C φ) Z ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta φ Z ξ := by
  have h := FieldFinite.CM.source_field_finite_theta_series A (Equiv.refl _) C.rationalPosition φ Z ξ
  refine Eq.trans ?_ h
  apply tsum_congr
  intro x
  change _ * RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue Z ξ (fun i => (C.rationalPosition x i : ℝ)) =
    _ * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel Z (C.rationalPosition x) ξ
  congr 1
  simp only [RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.kernel, RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.realPosition,
    ComplexMultiplication.ThetaCoordinates.CM.thetaCoordinatePairing_apply]
  rfl

theorem comparison_input_completed_theta (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C (comparisonFiniteInput C φ) Z.matrix ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  rw [RepresentationTheory.Theta.Adelic.DataTheta.completedTheta, IntrinsicReference.CM.native_completion_form_eq, comparison_input_rational_theta]
  rfl

def comparisonSourceInput
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m)) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) :=
  ⟨(IntrinsicFiniteTestReturn.CM.nativeFiniteBasisReturn A C.rationalPosition f).val,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp
      (IntrinsicFiniteTestReturn.CM.nativeFiniteBasisReturn A C.rationalPosition f).property⟩

theorem comparison_source_input_weight
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (x : RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.Position F (3 * m)) :
    (comparisonSourceInput C f).val (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.diagonal (C.rationalPosition x)) =
      RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) f (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) :=
  IntrinsicFiniteTestReturn.CM.native_finite_basis_return_value A C.rationalPosition f x

theorem comparison_source_rational_theta
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : Matrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) ℂ) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta C f Z ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.theta (comparisonSourceInput C f) Z ξ := by
  rw [← comparison_input_rational_theta C (comparisonSourceInput C f)]
  apply tsum_congr
  intro x
  change _ * _ =
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction F (3 * m) (comparisonFiniteInput C (comparisonSourceInput C f))
      (RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) * _
  rw [comparisonFiniteInput, FieldFinite.CM.source_field_finite_input_weight]
  exact congrArg (fun a : ℂ => a * RepresentationTheory.Theta.Adelic.DataTheta.gaussianValue Z ξ
    (fun i => (C.rationalPosition x i : ℝ))) (comparison_source_input_weight C f x).symm

theorem comparison_source_completed_theta
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz F (3 * m))
    (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A)) (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta C f Z.matrix ξ = RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (comparisonSourceInput C f) Z ξ := by
  rw [RepresentationTheory.Theta.Adelic.DataTheta.completedTheta, IntrinsicReference.CM.native_completion_form_eq, comparison_source_rational_theta]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Comparison.CM
