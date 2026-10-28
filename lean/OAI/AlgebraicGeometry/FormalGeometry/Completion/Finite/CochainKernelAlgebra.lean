import OAI.AlgebraicGeometry.FormalGeometry.Completion.KernelAlgebraNaturality
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CochainZero
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleTensor

/-! # Cochain Kernel Algebra -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CochainKernelAlgebra

noncomputable section

/-! A finite projective cochain model represents degree-zero cycles
of the actual complex after every scalar tensor for which it is a quasi-isomorphism. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory

namespace Construction

universe u
variable {R : Type u} [CommRing R]
  {C D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)
  [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
  [Module.Finite R (C.X 1)] [Module.Projective R (C.X 1)]

abbrev cochainKernelAlgebra := ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebra R (C.X 0) (C.d 0 1).hom

def cochainKernelAlgebraEquiv (A : Type u) [CommRing A] [Algebra R A]
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) 0] :
    ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A D).d 0 1).hom.ker ≃ (cochainKernelAlgebra (C := C) →ₐ[R] A) :=
  (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ)).symm.toEquiv.trans
    (ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R (C.X 0) (C.d 0 1).hom A)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CochainKernelAlgebra
