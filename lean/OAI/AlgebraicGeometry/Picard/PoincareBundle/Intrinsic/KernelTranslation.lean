import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelScalarRecovery

/-! # Kernel Translation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.KernelTranslation

noncomputable section

/-! Native kernel translations preserve the actual product cover and agree with PoincareBundle's kernel presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A B Q T : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]

/-- The product cover identifies a point and its actual native kernel translate. -/
theorem cover (a : T ⟶ Q) (x : T ⟶ A) (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme f) :
    lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f)) ≫ (𝟙 Q ⊗ₘ f) = lift a x ≫ (𝟙 Q ⊗ₘ f) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using Homomorphisms.LineKernelCocycle.Construction.kernel_translate_comp f x b

omit [IsMonHom f] in
/-- At the identity, the native and fiber-product kernel translations have the same actual endpoint. -/
theorem at_identity (b : T ⟶ Homomorphisms.Kernel.Construction.kernelScheme f) :
    ((b ≫ (Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso f).hom) ≫ Kernel.Scheme.kernelInclusion f) * (1 : T ⟶ A) =
      (1 : T ⟶ A) * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f) := by
  rw [Category.assoc, Homomorphisms.KernelGroup.Construction.kernelSchemePullbackIso_inclusion, mul_one, one_mul]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Intrinsic.KernelTranslation
