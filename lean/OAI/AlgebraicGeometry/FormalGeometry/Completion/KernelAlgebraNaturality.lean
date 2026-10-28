import OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.ProjectiveKernelAlgebra

/-! # Kernel Algebra Naturality -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.KernelAlgebraNaturality.Construction

noncomputable section

/-! The affine algebra representing the differential kernel is natural
in the coefficient algebra, including non-flat base changes. -/

open scoped TensorProduct

universe u v w t s
variable (R : Type u) [CommRing R]
  (P : Type v) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
  {Q : Type t} [AddCommGroup Q] [Module R Q] [Module.Finite R Q] [Module.Projective R Q]
  (d : P →ₗ[R] Q)
  {M : Type w} [AddCommGroup M] [Module R M]
  {N : Type s} [AddCommGroup N] [Module R N]

theorem finiteProjectiveTensorDualEquiv_natural (h : M →ₗ[R] N)
    (x : TensorProduct R M P) (φ : Module.Dual R P) :
    Completion.Finite.ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P N (h.rTensor P x) φ =
      h (Completion.Finite.ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P M x φ) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p =>
    change φ p • h m = h (φ p • m)
    exact (h.map_smul _ _).symm
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

omit [Module.Finite R P] [Module.Projective R P] [Module.Finite R Q] [Module.Projective R Q] in
theorem tensorDifferential_natural (h : M →ₗ[R] N) (x : TensorProduct R M P) :
    d.lTensor N (h.rTensor P x) = h.rTensor Q (d.lTensor M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul m p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def finiteProjectiveKernelMap (h : M →ₗ[R] N) :
    LinearMap.ker (d.lTensor M) →ₗ[R] LinearMap.ker (d.lTensor N) :=
  ((h.rTensor P).comp (LinearMap.ker (d.lTensor M)).subtype).codRestrict _ (by
    intro x
    change d.lTensor N (h.rTensor P (x : TensorProduct R M P)) = 0
    rw [tensorDifferential_natural R P d h, x.property, map_zero])

variable (A : Type w) [CommRing A] [Algebra R A]

theorem finiteProjectiveKernelAlgebraEquiv_ι (x : LinearMap.ker (d.lTensor A)) (φ : Module.Dual R P) :
    Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R P d A x
      (SymmetricAlgebra.ι R (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelDualModule R P d) (Submodule.Quotient.mk φ)) =
      Completion.Finite.ProjectiveTensorDual.Construction.finiteProjectiveTensorDualEquiv R P A x φ := by
  change SymmetricAlgebra.lift (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelToHom R P d A x)
    (SymmetricAlgebra.ι R _ (Submodule.Quotient.mk φ)) = _
  rw [SymmetricAlgebra.lift_ι_apply]
  rfl

theorem finiteProjectiveKernelAlgebraEquiv_natural
    {B : Type s} [CommRing B] [Algebra R B] (h : A →ₐ[R] B) (x : LinearMap.ker (d.lTensor A)) :
    Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R P d B (finiteProjectiveKernelMap R P d h.toLinearMap x) =
      h.comp (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R P d A x) := by
  apply SymmetricAlgebra.algHom_ext
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H φ =>
    change Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R P d B (finiteProjectiveKernelMap R P d h.toLinearMap x)
        (SymmetricAlgebra.ι R _ (Submodule.Quotient.mk φ)) =
      h (Completion.Finite.ProjectiveKernelAlgebra.Construction.finiteProjectiveKernelAlgebraEquiv R P d A x (SymmetricAlgebra.ι R _ (Submodule.Quotient.mk φ)))
    rw [finiteProjectiveKernelAlgebraEquiv_ι, finiteProjectiveKernelAlgebraEquiv_ι]
    exact finiteProjectiveTensorDualEquiv_natural R P h.toLinearMap x φ

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.KernelAlgebraNaturality.Construction
