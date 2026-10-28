import OAI.RepresentationTheory.Theta.Geometric.Dual.SectionEvaluation
import OAI.RepresentationTheory.Theta.Geometric.Dual.CoefficientHolomorphic

/-! # Tensor Local Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.TensorLocalHolomorphic

noncomputable section

/-! Local holomorphy of both coefficients on a scalar-extended affine
chart. Only differentiability at the point being evaluated is needed. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.Manifold

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem dualTensorEvaluation_coefficients_differentiableAt
    {A : Type*} [CommRing A] [Algebra ℂ A] (p : V → (A →ₐ[ℂ] ℂ)) (z : V)
    (hp : ∀ r, DifferentiableAt ℂ (fun w => p w r) z) (u : DualNumber ℂ ⊗[ℂ] A) :
    CoefficientHolomorphic.DualCoefficientDifferentiableAt (fun w => TensorEvaluation.dualTensorEvaluation (p w) u) z := by
  induction u using TensorProduct.inductionOn with
  | tmul c r =>
    constructor
    · simpa only [TensorEvaluation.dualTensorEvaluation_tmul_fst] using (hp r).const_mul c.fst
    · simpa only [TensorEvaluation.dualTensorEvaluation_tmul_snd] using (hp r).const_mul c.snd
  | add u v hu hv =>
    constructor
    · simpa only [map_add, TrivSqZeroExt.fst_add] using hu.1.fun_add hv.1
    · simpa only [map_add, TrivSqZeroExt.snd_add] using hu.2.fun_add hv.2

theorem nativeDualTensorEvaluation_coefficients_differentiableAt
    (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] [IsIntegral X.left] [Smooth X.hom]
    (p : V → AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (z : V)
    (hp : MDifferentiableAt (𝓘(ℂ, V))
      (𝓘(ℂ, Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) p z)
    (u : DualNumber ℂ ⊗[ℂ] Γ(X.left, ⊤)) :
    CoefficientHolomorphic.DualCoefficientDifferentiableAt
      (fun w => TensorEvaluation.dualTensorEvaluation (AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X (p w)) u) z := by
  apply dualTensorEvaluation_coefficients_differentiableAt
  intro r
  have heq : (fun w => AlgebraicGeometry.Foundations.Scheme.AffineSchemeComplexPoints.affineNativePointEquiv X (p w) r) = RegularFunctionContinuity.regularFunctionValue X r ∘ p :=
    funext (fun w => SectionEvaluation.affineNativePointEquiv_regularFunctionValue X (p w) r)
  rw [heq]
  exact (((OpenRegularFunctionValues.regularFunctionValue_contMDiff X r 1).mdifferentiableAt one_ne_zero).comp z hp).differentiableAt

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.TensorLocalHolomorphic
