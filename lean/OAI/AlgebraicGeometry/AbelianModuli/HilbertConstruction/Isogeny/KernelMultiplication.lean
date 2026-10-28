import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.KernelZeroSection

/-! # Kernel Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Multiplication on the actual isogeny kernel is constructed through its functor of points and commutes with the kernel inclusion. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

variable {S : Scheme.{u}} {g h : ℕ} {A : Abelian.Schemes.AbelianScheme g S} {B : Abelian.Schemes.AbelianScheme h S}
variable (p : Abelian.Schemes.AbelianScheme.Isogeny A B)

def Abelian.Schemes.AbelianScheme.Isogeny.kernelMultiplication (n : ℕ) : p.kernelScheme ⟶ p.kernelScheme :=
  (p.kernelSchemePointsEquiv _).symm ⟨p.kernelInclusion ^ n, by
    change (p.kernelInclusion ^ n) ≫ p.hom = 1
    rw [MonObj.pow_comp, Abelian.Schemes.AbelianScheme.Isogeny.kernelInclusion_comp, one_pow]⟩

@[reassoc (attr := simp)] theorem Abelian.Schemes.AbelianScheme.Isogeny.kernelMultiplication_inclusion (n : ℕ) :
    p.kernelMultiplication n ≫ p.kernelInclusion = p.kernelInclusion ^ n :=
  congrArg (fun x : p.kernelAt p.kernelScheme => x.val)
    ((p.kernelSchemePointsEquiv _).apply_symm_apply _)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
