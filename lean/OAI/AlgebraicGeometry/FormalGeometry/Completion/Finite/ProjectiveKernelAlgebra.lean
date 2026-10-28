import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveTensorDual
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic

/-! # Projective Kernel Algebra -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveKernelAlgebra.Construction

noncomputable section

/-! The kernel of a map between finite projective modules, after every
base extension, is represented by the symmetric algebra of the dual cokernel. -/

open scoped TensorProduct

universe u v w t
variable (R : Type u) [CommRing R]
  (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  {Q : Type t} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
  (d : P →ₗ[R] Q)

abbrev finiteProjectiveKernelDualModule := Module.Dual R P ⧸ LinearMap.range d.dualMap

variable (M : Type w) [AddCommGroup M] [Module R M]

def finiteProjectiveKernelToHom (x : LinearMap.ker (d.lTensor M)) :
    finiteProjectiveKernelDualModule R P d →ₗ[R] M :=
  (LinearMap.range d.dualMap).liftQ (ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M x) (by
    rintro φ ⟨ψ, rfl⟩
    exact (ProjectiveTensorDual.Construction.finiteProjectiveTensor_kernel_iff R P M d x).mp x.property ψ)

def finiteProjectiveHomToKernel (F : finiteProjectiveKernelDualModule R P d →ₗ[R] M) :
    LinearMap.ker (d.lTensor M) :=
  ⟨(ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M).symm (F.comp (LinearMap.range d.dualMap).mkQ), by
    apply (ProjectiveTensorDual.Construction.finiteProjectiveTensor_kernel_iff R P M d _).mpr
    intro ψ
    rw [LinearEquiv.apply_symm_apply]
    change F ((LinearMap.range d.dualMap).mkQ (d.dualMap ψ)) = 0
    have hz : (LinearMap.range d.dualMap).mkQ (d.dualMap ψ) = 0 := by
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range d.dualMap)).mpr (LinearMap.mem_range_self _ _)
    rw [hz, map_zero]⟩

def finiteProjectiveKernelHomEquiv : LinearMap.ker (d.lTensor M) ≃
    (finiteProjectiveKernelDualModule R P d →ₗ[R] M) where
  toFun := finiteProjectiveKernelToHom R P d M
  invFun := finiteProjectiveHomToKernel R P d M
  left_inv x := by
    apply Subtype.ext
    apply (ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M).injective
    change ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M
      ((ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M).symm
        ((finiteProjectiveKernelToHom R P d M x).comp (LinearMap.range d.dualMap).mkQ)) = _
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro φ
    rfl
  right_inv F := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H φ =>
      change ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M
        ((ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M).symm (F.comp (LinearMap.range d.dualMap).mkQ)) φ = _
      rw [LinearEquiv.apply_symm_apply]
      rfl

abbrev finiteProjectiveKernelAlgebra := SymmetricAlgebra R (finiteProjectiveKernelDualModule R P d)

variable (A : Type w) [CommRing A] [Algebra R A]

def finiteProjectiveKernelAlgebraEquiv :
    LinearMap.ker (d.lTensor A) ≃ (finiteProjectiveKernelAlgebra R P d →ₐ[R] A) :=
  (finiteProjectiveKernelHomEquiv R P d A).trans SymmetricAlgebra.lift

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveKernelAlgebra.Construction
