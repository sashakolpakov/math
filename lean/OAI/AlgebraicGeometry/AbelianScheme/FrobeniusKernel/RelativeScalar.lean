import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar

/-! # Relative Scalar -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeScalar.Construction

noncomputable section

/-! Proper-group functions turn native descent cocycles into kernel
characters. The scalar argument works over arbitrary parameter schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar.Construction

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable {f : A ⟶ B} [IsMonHom f]
variable [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) A).left.appTop]

theorem kernelCocycle_value_eq_scalar_of_functions (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)
    {T : Over S} (x : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    D.value x z = z.left.appTop D.kernelScalar := by
  let K := Picard.Homomorphisms.Kernel.Construction.kernelScheme f
  let P := K ⊗ A
  let j : K ⟶ P := lift (𝟙 K) (1 : K ⟶ A)
  let a : Γ(P.left, ⊤) := D.value (snd K A) (fst K A)
  have hji : j ≫ fst K A = 𝟙 K := lift_fst _ _
  have hjx : j ≫ snd K A = 1 := lift_snd _ _
  have hj : j.left.appTop a = D.kernelScalar := by
    rw [show j.left.appTop a = D.value (j ≫ snd K A) (j ≫ fst K A) from
      D.naturality j (snd K A) (fst K A), hji, hjx]
    rfl
  have hs : (fst K A).left.appTop ≫ j.left.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, hji, Over.id_left, Scheme.Hom.id_appTop]
  have hs' : j.left.appTop ≫ (fst K A).left.appTop = 𝟙 _ := by
    apply (cancel_epi (fst K A).left.appTop).mp
    rw [← Category.assoc, hs, Category.id_comp, Category.comp_id]
  have ha : (fst K A).left.appTop D.kernelScalar = a := by
    rw [← hj]
    exact ConcreteCategory.congr_hom hs' a
  let t : T ⟶ P := lift z x
  have ht : D.value x z = t.left.appTop a := by
    rw [show t.left.appTop a = D.value (t ≫ snd K A) (t ≫ fst K A) from
      D.naturality t (snd K A) (fst K A), lift_fst, lift_snd]
  rw [ht, ← ha]
  change ((fst K A).left.appTop ≫ t.left.appTop) D.kernelScalar = _
  rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, lift_fst]

theorem kernelCocycle_value_independent_of_functions (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)
    {T : Over S} (x y : T ⟶ A) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    D.value x z = D.value y z := by
  rw [kernelCocycle_value_eq_scalar_of_functions D x z, kernelCocycle_value_eq_scalar_of_functions D y z]

theorem kernelCocycle_scalar_mul_of_functions (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)
    {T : Over S} (z w : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :
    (z * w).left.appTop D.kernelScalar =
      z.left.appTop D.kernelScalar * w.left.appTop D.kernelScalar := by
  rw [← kernelCocycle_value_eq_scalar_of_functions D (1 : T ⟶ A) (z * w),
    ← D.cocycle, kernelCocycle_value_eq_scalar_of_functions D, kernelCocycle_value_eq_scalar_of_functions D]

theorem kernelCocycle_scalar_one_of_functions (D : Picard.Homomorphisms.KernelScalar.Construction.KernelScalarCocycle f)
    (T : Over S) :
    (1 : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left.appTop D.kernelScalar = 1 := by
  rw [← kernelCocycle_value_eq_scalar_of_functions D (1 : T ⟶ A) 1, D.unit]

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.RelativeScalar.Construction
