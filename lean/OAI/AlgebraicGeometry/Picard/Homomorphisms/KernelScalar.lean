import OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelGroup
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions

/-! # Kernel Scalar -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar

noncomputable section

/-! A scalar cocycle for the action of the actual kernel of a group
morphism. Properness makes the cocycle independent of the abelian-variety
coordinate, leaving a multiplicative scalar on the kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f]

structure KernelScalarCocycle where
  value {T : Over S} (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) : Γ(T.left, ⊤)
  isUnit {T : Over S} (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) : IsUnit (value x z)
  naturality {T T' : Over S} (t : T' ⟶ T) (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) :
    t.left.appTop (value x z) = value (t ≫ x) (t ≫ z)
  unit {T : Over S} (x : T ⟶ A) : value x 1 = 1
  cocycle {T : Over S} (x : T ⟶ A) (z w : T ⟶ Kernel.Construction.kernelScheme f) :
    value x z * value (x * (z ≫ Kernel.Construction.kernelInclusion f)) w = value x (z * w)

variable {f}

def KernelScalarCocycle.kernelScalar (D : KernelScalarCocycle f) : Γ((Kernel.Construction.kernelScheme f).left, ⊤) :=
  D.value 1 (𝟙 _)

theorem KernelScalarCocycle.kernelScalar_isUnit (D : KernelScalarCocycle f) :
    IsUnit D.kernelScalar := D.isUnit _ _

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable {f : A ⟶ B} [IsMonHom f]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable [IsAffine (Kernel.Construction.kernelScheme f).left]

theorem KernelScalarCocycle.value_eq_kernelScalar (D : KernelScalarCocycle f)
    {T : Over (Spec (.of k))} (x : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) :
    D.value x z = z.left.appTop D.kernelScalar := by
  let K := Kernel.Construction.kernelScheme f
  let P := K ⊗ A
  let j : K ⟶ P := lift (𝟙 K) (1 : K ⟶ A)
  let a : Γ(P.left, ⊤) := D.value (snd K A) (fst K A)
  have hji : j ≫ fst K A = 𝟙 K := lift_fst _ _
  have hjx : j ≫ snd K A = 1 := lift_snd _ _
  have hj : j.left.appTop a = D.kernelScalar := by
    rw [show j.left.appTop a = D.value (j ≫ snd K A) (j ≫ fst K A) from
      D.naturality j (snd K A) (fst K A), hji, hjx]
    rfl
  have : IsIso (fst K A).left.appTop := ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso A K
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

theorem KernelScalarCocycle.value_independent (D : KernelScalarCocycle f)
    {T : Over (Spec (.of k))} (x y : T ⟶ A) (z : T ⟶ Kernel.Construction.kernelScheme f) :
    D.value x z = D.value y z := by
  rw [D.value_eq_kernelScalar x z, D.value_eq_kernelScalar y z]

theorem KernelScalarCocycle.kernelScalar_mul (D : KernelScalarCocycle f)
    {T : Over (Spec (.of k))} (z w : T ⟶ Kernel.Construction.kernelScheme f) :
    (z * w).left.appTop D.kernelScalar =
      z.left.appTop D.kernelScalar * w.left.appTop D.kernelScalar := by
  rw [← D.value_eq_kernelScalar (1 : T ⟶ A) (z * w),
    ← D.cocycle, D.value_eq_kernelScalar, D.value_eq_kernelScalar]

theorem KernelScalarCocycle.kernelScalar_one (D : KernelScalarCocycle f)
    (T : Over (Spec (.of k))) :
    (1 : T ⟶ Kernel.Construction.kernelScheme f).left.appTop D.kernelScalar = 1 := by
  rw [← D.value_eq_kernelScalar (1 : T ⟶ A) 1, D.unit]

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.KernelScalar
