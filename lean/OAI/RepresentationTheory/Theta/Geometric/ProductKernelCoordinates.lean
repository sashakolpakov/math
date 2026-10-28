import OAI.RepresentationTheory.Theta.Geometric.KernelTransportComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-! # Product Kernel Coordinates -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductKernelCoordinates

noncomputable section

/-! The actual kernel of the product isogeny acts by translation in
its first coordinate on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme
attribute [local instance] AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelGroup

variable {g h : ℕ} {A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {B : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (p : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def productKernelFirst (T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) :
    (T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme)) →* p.kernelAt T where
  toFun k := ⟨k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ fst A.scheme A.scheme, by
    change (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ fst A.scheme A.scheme) ≫ p.hom = 1
    have hk : k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) = 1 := by
      rw [AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
    have hh := congrArg (fun a => a ≫ fst B.scheme A.scheme) hk
    simpa only [Category.assoc, tensorHom_fst, MonObj.one_comp] using hh⟩
  map_one' := Subtype.ext (by simp only [MonObj.one_comp]; rfl)
  map_mul' k l := Subtype.ext (by simp only [MonObj.mul_comp]; rfl)

theorem productKernel_second {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme)) :
    k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ snd A.scheme A.scheme = 1 := by
  have hk : k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme) ≫ (p.hom ⊗ₘ 𝟙 A.scheme) = 1 := by
    rw [AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion_comp, MonObj.comp_one]
  have hh := congrArg (fun a => a ≫ snd B.scheme A.scheme) hk
  simpa only [Category.assoc, tensorHom_snd, Category.comp_id, MonObj.one_comp] using hh

theorem productKernelFirst_natural {T U : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (j : U ⟶ T)
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme)) :
    IsogenyKernelScheme.isogenyKernelPullback p j (productKernelFirst p T k) = productKernelFirst p U (j ≫ k) := by
  apply Subtype.ext
  exact (Category.assoc j k _).symm

theorem productKernel_translate {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x : T ⟶ A.scheme ⊗ A.scheme)
    (k : T ⟶ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelObject (p.hom ⊗ₘ 𝟙 A.scheme)) :
    x * (k ≫ AlgebraicGeometry.Picard.PoincareBundle.Kernel.Scheme.kernelInclusion (p.hom ⊗ₘ 𝟙 A.scheme)) =
      KernelDifferenceTransport.firstKernelTranslate A.scheme x (productKernelFirst p T k).val := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [KernelDifferenceTransport.firstKernelTranslate, lift_fst, MonObj.mul_comp, Category.assoc]
    rfl
  · simp only [KernelDifferenceTransport.firstKernelTranslate, lift_snd, MonObj.mul_comp, Category.assoc,
      productKernel_second, mul_one]

end

end OAI.RepresentationTheory.Theta.Geometric.ProductKernelCoordinates
