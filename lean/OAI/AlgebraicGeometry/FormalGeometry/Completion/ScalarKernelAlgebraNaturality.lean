import OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelTransition

/-! # Scalar Kernel Algebra Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelAlgebraNaturality

noncomputable section

/-! The classifying algebra respects the explicit transition between
categorical scalar-extension kernels, with a specified composite ring map. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory

namespace Construction

universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  (f : R →+* S) (g : S →+* T) (k : R →+* T) (h : g.comp f = k)

def scalarTransitionAlgHomOfEq :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := k.toAlgebra
    S →ₐ[R] T := by
  subst k
  exact ScalarKernelTransition.Construction.scalarTransitionAlgHom f g

theorem scalarTransitionAlgHomOfEq_apply (a : S) :
    scalarTransitionAlgHomOfEq f g k h a = g a := by
  subst k
  rfl

variable (C : CochainComplex (ModuleCat.{u} R) ℕ)
  [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
  [Module.Finite R (C.X 1)] [Module.Projective R (C.X 1)]

def scalarKernelAlgebraEquiv :
    letI : Algebra R S := f.toAlgebra
    ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker ≃
      (Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebra (C := C) →ₐ[R] S) := by
  letI : Algebra R S := f.toAlgebra
  exact (ScalarExtensionKernel.Construction.scalarExtensionKernelEquiv f C).trans
    (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R (C.X 0) (C.d 0 1).hom S)

theorem scalarKernelAlgebraEquiv_natural
    (x : ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := k.toAlgebra
    scalarKernelAlgebraEquiv k C (ScalarKernelTransition.Construction.scalarCochainKernelTransitionOfEq f g k h C x) =
      (scalarTransitionAlgHomOfEq f g k h).comp (scalarKernelAlgebraEquiv f C x) := by
  subst k
  let : Algebra R S := f.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  exact KernelAlgebraNaturality.Construction.finiteProjectiveKernelAlgebraEquiv_natural R (C.X 0) (C.d 0 1).hom S
    (ScalarKernelTransition.Construction.scalarTransitionAlgHom f g) (ScalarExtensionKernel.Construction.scalarExtensionKernelEquiv f C x)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarKernelAlgebraNaturality
