import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalExtension
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Rational Algebra -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison

noncomputable section

/-! Actual rational pullback reverses multiplication. Commutativity of
the spherical algebra turns this into the required algebra action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

theorem RationalAlgebra.rationalExtensionOfAddHom_mul {R V : Type*} [Ring R] [Ring V] [Algebra ℚ V]
    (f : R →+ V) (hmul : ∀ a b, f (a * b) = f b * f a) (x y : ℚ ⊗[ℤ] R) :
    RationalExtension.rationalExtensionOfAddHom f (x * y) = RationalExtension.rationalExtensionOfAddHom f y * RationalExtension.rationalExtensionOfAddHom f x := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [add_mul, map_add, hx, hz, mul_add]
  | tmul r a =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [mul_add, map_add, hy, hz, add_mul]
    | tmul t b =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, RationalExtension.rationalExtensionOfAddHom_tmul,
        RationalExtension.rationalExtensionOfAddHom_tmul, RationalExtension.rationalExtensionOfAddHom_tmul, hmul, smul_mul_smul]
      rw [mul_comm r t]

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : Data.SphericalPELAlbaneseData E K s q)
  (hadd : ∀ a b : D.EndK, D.pullbackH1Integral (a + b) = D.pullbackH1Integral a + D.pullbackH1Integral b)

theorem Data.SphericalPELAlbaneseData.rationalH1Pullback_one : D.rationalH1Pullback hadd 1 = 1 := by
  change RationalExtension.rationalExtensionOfAddHom (D.integralH1PullbackAddHom hadd) (1 ⊗ₜ[ℤ] (1 : D.EndK)) = _
  rw [RationalExtension.rationalExtensionOfAddHom_tmul, one_smul]
  exact D.pullbackH1Integral_one

theorem Data.SphericalPELAlbaneseData.rationalH1Pullback_mul (x y : D.EndQ) :
    D.rationalH1Pullback hadd (x * y) = D.rationalH1Pullback hadd y * D.rationalH1Pullback hadd x :=
  RationalAlgebra.rationalExtensionOfAddHom_mul (D.integralH1PullbackAddHom hadd) (D.pullbackH1Integral_mul) x y

def Data.SphericalPELAlbaneseData.rationalH1OppositeAction : D.EndQᵐᵒᵖ →ₐ[ℚ] Module.End ℚ D.H1 where
  toFun x := D.rationalH1Pullback hadd x.unop
  map_zero' := map_zero _
  map_add' x y := map_add _ x.unop y.unop
  map_one' := D.rationalH1Pullback_one hadd
  map_mul' x y := D.rationalH1Pullback_mul hadd y.unop x.unop
  commutes' r := by
    change D.rationalH1Pullback hadd (algebraMap ℚ D.EndQ r) = algebraMap ℚ (Module.End ℚ D.H1) r
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Data.SphericalPELAlbaneseData.rationalH1Pullback_one,
      Algebra.algebraMap_eq_smul_one]

def Data.SphericalPELAlbaneseData.sphericalActionOpposite (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (ρ : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ) :
    HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQᵐᵒᵖ where
  toFun x := MulOpposite.op (ρ x)
  map_zero' := congrArg MulOpposite.op ρ.map_zero
  map_add' x y := congrArg MulOpposite.op (ρ.map_add x y)
  map_one' := congrArg MulOpposite.op ρ.map_one
  map_mul' x y := congrArg MulOpposite.op
    ((congrArg ρ (Commutativity.spherical_mul_comm s q hElementaryDivisors x y)).trans (ρ.map_mul y x))
  commutes' r := congrArg MulOpposite.op (ρ.commutes r)

def Data.SphericalPELAlbaneseData.sphericalH1Action (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (ρ : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ) :
    HeckeKernel.Hecke s q →ₐ[ℚ] Module.End ℚ D.H1 :=
  (D.rationalH1OppositeAction hadd).comp (D.sphericalActionOpposite hElementaryDivisors ρ)

theorem Data.SphericalPELAlbaneseData.sphericalH1Action_spec (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (ρ : HeckeKernel.Hecke s q →ₐ[ℚ] D.EndQ)
    (h : HeckeKernel.Hecke s q) : D.IsRationalH1Pullback (ρ h) (D.sphericalH1Action hadd hElementaryDivisors ρ h) :=
  D.rationalH1Pullback_spec hadd (ρ h)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison
