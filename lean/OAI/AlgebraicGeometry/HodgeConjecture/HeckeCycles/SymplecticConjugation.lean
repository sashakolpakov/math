import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic

/-! # Symplectic Conjugation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticConjugation.CM

noncomputable section

/-! Exact Jacobi and Gaussian identities for conjugation by a rational
symplectic change of frame. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction

variable {I : Type} [Fintype I] [DecidableEq I]

theorem blocks (S g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) :
    RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.composeBlocks (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (S * g * S⁻¹)) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) =
      RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.composeBlocks (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g) := by
  rw [← RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.realBlocks_mul, ← RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.realBlocks_mul]
  congr 1
  group

theorem jacobi (S g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (S * g * S⁻¹)).jacobiChange ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).transformSiegel Z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).jacobiChange Z ξ) =
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).jacobiChange ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).transformSiegel Z)
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).jacobiChange Z ξ) := by
  rw [← RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.compose_jacobiChange, blocks, RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.compose_jacobiChange]

theorem quadratic (S g : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (ξ : I → ℂ) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) Z ξ *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (S * g * S⁻¹)) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).transformSiegel Z)
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S).jacobiChange Z ξ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g) Z ξ *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).transformSiegel Z)
          ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks g).jacobiChange Z ξ) := by
  rw [← RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.compose_quadraticFactor, blocks, RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.compose_quadraticFactor]

theorem jacobi_surjective (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks I ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) :
    Function.Surjective (g.jacobiChange Z) := by
  intro ξ
  refine ⟨(g.complexify.denominator Z.matrix).transpose *ᵥ ξ, ?_⟩
  rw [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z), Matrix.transpose_one, Matrix.one_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SymplecticConjugation.CM
