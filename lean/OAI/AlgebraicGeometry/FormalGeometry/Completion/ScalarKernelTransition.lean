import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarExtensionKernel
import OAI.AlgebraicGeometry.FormalGeometry.Completion.KernelAlgebraNaturality

/-! # Scalar Kernel Transition -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelTransition

noncomputable section

/-! Explicit transitions between scalar-extended differential kernels
for composable ring maps, compatible with the classifying algebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace Construction

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T)

def scalarTransitionAlgHom :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := (g.comp f).toAlgebra
    S →ₐ[R] T := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := (g.comp f).toAlgebra
  exact { __ := g, commutes' := fun _ => rfl }

def scalarCochainTransitionAt (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (ModuleCat.extendScalars f).obj (C.X q) →+ (ModuleCat.extendScalars (g.comp f)).obj (C.X q) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := (g.comp f).toAlgebra
  exact ((scalarTransitionAlgHom f g).toLinearMap.rTensor (C.X q)).toAddMonoidHom

theorem scalarCochainTransitionAt_tmul (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (a : S) (c : C.X q) :
    scalarCochainTransitionAt f g C q (a ⊗ₜ[R,f] c) = g a ⊗ₜ[R,g.comp f] c := rfl

def scalarCochainKernelTransition (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker →
      ((((ModuleCat.extendScalars (g.comp f)).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := (g.comp f).toAlgebra
  intro x
  exact ⟨scalarCochainTransitionAt f g C 0 x.val, by
    change (C.d 0 1).hom.lTensor T
      ((scalarTransitionAlgHom f g).toLinearMap.rTensor (C.X 0) x.val) = 0
    have hx : (C.d 0 1).hom.lTensor S x.val = 0 := x.property
    rw [KernelAlgebraNaturality.Construction.tensorDifferential_natural R (C.X 0) (C.d 0 1).hom, hx, map_zero]⟩

theorem scalarCochainKernelTransition_val (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (x : ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker) :
    (scalarCochainKernelTransition f g C x).val = scalarCochainTransitionAt f g C 0 x.val := rfl

variable (k : R →+* T) (h : g.comp f = k)

def scalarCochainTransitionAtOfEq (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ) :
    (ModuleCat.extendScalars f).obj (C.X q) →+ (ModuleCat.extendScalars k).obj (C.X q) := by
  subst k
  exact scalarCochainTransitionAt f g C q

theorem scalarCochainTransitionAtOfEq_tmul (C : CochainComplex (ModuleCat.{u} R) ℕ) (q : ℕ)
    (a : S) (c : C.X q) :
    scalarCochainTransitionAtOfEq f g k h C q (a ⊗ₜ[R,f] c) = g a ⊗ₜ[R,k] c := by
  subst k
  rfl

def scalarCochainKernelTransitionOfEq (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker →
      ((((ModuleCat.extendScalars k).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker := by
  subst k
  exact scalarCochainKernelTransition f g C

theorem scalarCochainKernelTransitionOfEq_val (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (x : ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker) :
    (scalarCochainKernelTransitionOfEq f g k h C x).val = scalarCochainTransitionAtOfEq f g k h C 0 x.val := by
  subst k
  rfl

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelTransition
