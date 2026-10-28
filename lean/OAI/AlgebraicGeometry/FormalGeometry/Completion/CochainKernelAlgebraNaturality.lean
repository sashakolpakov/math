import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.CochainKernelAlgebra

/-! # Cochain Kernel Algebra Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainKernelAlgebraNaturality

noncomputable section

/-! The degree-zero representation commutes with arbitrary coefficient
maps through the actual cochain comparison. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory

namespace Construction

universe u
variable {R : Type u} [CommRing R]
  (C : CochainComplex (ModuleCat.{u} R) ℕ)
  {A B : Type u} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def cochainTensorKernelMap (h : A →ₗ[R] B) :
    ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A C).d 0 1).hom.ker →ₗ[R]
      ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex B C).d 0 1).hom.ker :=
  ((h.rTensor (C.X 0)).comp (LinearMap.ker ((C.d 0 1).hom.lTensor A)).subtype).codRestrict _ (by
    intro x
    change (C.d 0 1).hom.lTensor B (h.rTensor (C.X 0) x.val) = 0
    rw [KernelAlgebraNaturality.Construction.tensorDifferential_natural R (C.X 0) (C.d 0 1).hom h, x.property, map_zero])

variable {C} {D : CochainComplex (ModuleCat.{u} R) ℕ} (φ : C ⟶ D)

theorem cochainTensorKernelEquiv_natural (h : A →ₗ[R] B)
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) 0]
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map B φ) 0]
    (x : ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A C).d 0 1).hom.ker) :
    Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map B φ) (cochainTensorKernelMap C h x) =
      cochainTensorKernelMap D h
        (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) x) := by
  apply Subtype.ext
  rw [Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
  change (φ.f 0).hom.lTensor B (h.rTensor (C.X 0) x.val) =
    h.rTensor (D.X 0)
      (Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) x).val
  rw [Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv_apply_val]
  exact KernelAlgebraNaturality.Construction.tensorDifferential_natural R (C.X 0) (φ.f 0).hom h x.val

variable [Module.Finite R (C.X 0)] [Module.Projective R (C.X 0)]
  [Module.Finite R (C.X 1)] [Module.Projective R (C.X 1)]

theorem cochainKernelAlgebraEquiv_natural
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (h : A →ₐ[R] B)
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ) 0]
    [QuasiIsoAt (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map B φ) 0]
    (x : ((Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.complex A D).d 0 1).hom.ker) :
    Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebraEquiv φ B (cochainTensorKernelMap D h.toLinearMap x) =
      h.comp (Completion.Finite.CochainKernelAlgebra.Construction.cochainKernelAlgebraEquiv φ A x) := by
  let eA := Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map A φ)
  let eB := Quotients.FiniteDescent.CochainZero.Construction.CochainZeroCycles.kernelEquiv (Quotients.FiniteDescent.ModuleTensor.Construction.ModuleTensorFunctor.map B φ)
  have he : eB.symm (cochainTensorKernelMap D h.toLinearMap x) =
      cochainTensorKernelMap C h.toLinearMap (eA.symm x) := by
    apply eB.injective
    rw [eB.apply_symm_apply, cochainTensorKernelEquiv_natural, eA.apply_symm_apply]
  change Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R (C.X 0) (C.d 0 1).hom B
      (eB.symm (cochainTensorKernelMap D h.toLinearMap x)) =
    h.comp (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R (C.X 0) (C.d 0 1).hom A (eA.symm x))
  rw [he]
  exact KernelAlgebraNaturality.Construction.finiteProjectiveKernelAlgebraEquiv_natural R (C.X 0) (C.d 0 1).hom A h (eA.symm x)

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.CochainKernelAlgebraNaturality
