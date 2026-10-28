import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension

/-! # Contravariant Extension -/

namespace OAI.RepresentationTheory.Theta.Geometric.Rational.ContravariantExtension

noncomputable section

/-! Rational extension preserves the reversed composition law of
actual pullbacks. The proof uses the literal tensor-product arithmetic. -/

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension
open scoped TensorProduct

theorem rationalExtensionOfAddHom_mul_reverse
    {A B : Type*} [Ring A] [Ring B] [Algebra ℚ B]
    (f : A →+ B) (hf : ∀ a b, f (a * b) = f b * f a)
    (a b : ℚ ⊗[ℤ] A) :
    AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom f (a * b) =
      AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom f b * AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom f a := by
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
    induction b using TensorProduct.inductionOn with
    | tmul s b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom_tmul,
        AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom_tmul, AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom_tmul, hf]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    | add b c hb hc => simp only [mul_add, map_add, add_mul, hb, hc]
  | add a c ha hc => simp only [add_mul, map_add, mul_add, ha, hc]

theorem rationalExtensionOfAddHom_one
    {A B : Type*} [Ring A] [Ring B] [Algebra ℚ B]
    (f : A →+ B) (hf : f 1 = 1) : AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom f (1 : ℚ ⊗[ℤ] A) = 1 := by
  change AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom f (1 ⊗ₜ[ℤ] (1 : A)) = 1
  rw [AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension.rationalExtensionOfAddHom_tmul, one_smul, hf]

end

end OAI.RepresentationTheory.Theta.Geometric.Rational.ContravariantExtension
