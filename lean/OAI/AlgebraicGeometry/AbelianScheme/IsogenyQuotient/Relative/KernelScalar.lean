import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar

/-! # Kernel Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.KernelScalar.Construction

noncomputable section

/-! Independence of the source coordinate in a kernel scalar cocycle
uses only the actual global-functions isomorphism of the product
projection. This formulation applies to affine parameters over a field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar.Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  {f : A ⟶ B} [IsMonHom f]
  [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop] (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)

theorem kernelScalar_value_of_projection_functions {T : Over S}
    (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) : D.value x z = z.left.appTop D.kernelScalar := by
  let K := Picard.Homomorphisms.Kernel.Construction.kernelScheme f
  let j : K ⟶ K ⊗ A := lift (𝟙 K) (1 : K ⟶ A)
  let a : Γ((K ⊗ A).left, ⊤) := D.value (snd K A) (fst K A)
  have hj : j.left.appTop a = D.kernelScalar := by
    rw [show j.left.appTop a = D.value (j ≫ snd K A) (j ≫ fst K A) from
      D.naturality j (snd K A) (fst K A), lift_fst, lift_snd]
    rfl
  have hs : (fst K A).left.appTop ≫ j.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, lift_fst, Over.id_left, Scheme.Hom.id_appTop]
  have hs' : j.left.appTop ≫ (fst K A).left.appTop = 𝟙 _ := by
    apply (cancel_epi (fst K A).left.appTop).mp
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  have ha : (fst K A).left.appTop D.kernelScalar = a := by
    rw [← hj]
    exact ConcreteCategory.congr_hom hs' a
  let t : T ⟶ K ⊗ A := lift z x
  have ht : D.value x z = t.left.appTop a := by
    rw [show t.left.appTop a = D.value (t ≫ snd K A) (t ≫ fst K A) from
      D.naturality t (snd K A) (fst K A), lift_fst, lift_snd]
  rw [ht, ← ha]
  change ((fst K A).left.appTop ≫ t.left.appTop) D.kernelScalar = _
  rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, lift_fst]

theorem kernelScalar_mul_of_projection_functions {T : Over S} (z w : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    (z * w).left.appTop D.kernelScalar = z.left.appTop D.kernelScalar * w.left.appTop D.kernelScalar := by
  rw [← kernelScalar_value_of_projection_functions D (1 : T ⟶ A) (z * w),
    ← D.cocycle, kernelScalar_value_of_projection_functions, kernelScalar_value_of_projection_functions]

theorem kernelScalar_one_of_projection_functions (T : Over S) :
    (1 : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left.appTop D.kernelScalar = 1 := by
  rw [← kernelScalar_value_of_projection_functions D (1 : T ⟶ A) 1, D.unit]

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.KernelScalar.Construction
