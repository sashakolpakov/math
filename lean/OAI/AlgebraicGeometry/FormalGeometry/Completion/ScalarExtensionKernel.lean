import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CochainKernelAlgebra
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorExtensionQuasi

/-! # Scalar Extension Kernel -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarExtensionKernel

noncomputable section

/-! The underlying kernel of categorical scalar extension is the same
tensor kernel used by the explicit representing algebra. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory

namespace Construction

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (C : CochainComplex (ModuleCat.{u} R) ℕ)

def scalarExtensionKernelEquiv : letI : Algebra R S := f.toAlgebra
    ((((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).d 0 1).hom.ker ≃
      LinearMap.ker ((C.d 0 1).hom.lTensor S) := by
  letI : Algebra R S := f.toAlgebra
  exact { toFun x := ⟨x.val, x.property⟩
          invFun x := ⟨x.val, x.property⟩
          left_inv _ := rfl
          right_inv _ := rfl }

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ScalarExtensionKernel
