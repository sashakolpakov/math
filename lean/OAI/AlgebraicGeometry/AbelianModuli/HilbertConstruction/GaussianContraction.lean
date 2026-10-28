import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianCokernel

/-! # Gaussian Contraction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianContraction.LocalSectionLifting

noncomputable section

/-! The explicit contraction that removes an invertible differential block. -/

universe u v₁ v₂ v₃ v₄

variable {R : Type u} [CommRing R]
    {A : Type v₁} [AddCommGroup A] [Module R A]
    {B : Type v₂} [AddCommGroup B] [Module R B]
    {C : Type v₃} [AddCommGroup C] [Module R C]
    {D : Type v₄} [AddCommGroup D] [Module R D]
    (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D)

def blockSourceInclusion : A →ₗ[R] (A × B) :=
  (ComplexGaussian.LocalSectionLifting.blockSourceShear c d).toLinearMap.comp (LinearMap.inl R A B)

def blockContractingMap : (C × D) →ₗ[R] (A × B) :=
  (LinearMap.inr R A B).comp (d.symm.toLinearMap.comp (LinearMap.snd R C D))

theorem block_source_contraction (x : A × B) :
    blockSourceInclusion c d x.1 = x - blockContractingMap d (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d x) := by
  apply Prod.ext
  · simp [blockSourceInclusion, ComplexGaussian.LocalSectionLifting.blockSourceShear, blockContractingMap]
  · change 0 - d.symm (c x.1) = x.2 - d.symm (c x.1 + d x.2)
    simp only [map_add, LinearEquiv.symm_apply_apply]
    abel

theorem block_target_contraction (x : C × D) :
    (GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d x, (0 : D)) =
      x - ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (blockContractingMap d x) := by
  apply Prod.ext
  · change x.1 - b (d.symm x.2) = x.1 - (a 0 + b (d.symm x.2))
    simp
  · change 0 = x.2 - (c 0 + d (d.symm x.2))
    simp

theorem block_projection_differential (x : A × B) :
    GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d (ComplexGaussian.LocalSectionLifting.blockDifferential a b c d x) =
      ComplexGaussian.LocalSectionLifting.schurDifferential a b c d x.1 :=
  congrArg Prod.fst (ComplexGaussian.LocalSectionLifting.blockDifferential_target_coordinates a b c d x)

theorem block_differential_inclusion (x : A) :
    ComplexGaussian.LocalSectionLifting.blockDifferential a b c d (blockSourceInclusion c d x) =
      (ComplexGaussian.LocalSectionLifting.schurDifferential a b c d x, 0) :=
  ComplexGaussian.LocalSectionLifting.blockDifferential_lift_schur a b c d x

theorem block_source_retraction (x : A) : (blockSourceInclusion c d x).1 = x := rfl

theorem block_target_retraction (x : C) : GaussianCokernel.LocalSectionLifting.blockCokernelProjection b d (x, 0) = x := by
  simp [GaussianCokernel.LocalSectionLifting.blockCokernelProjection, ComplexGaussian.LocalSectionLifting.blockTargetShear]

theorem block_source_retraction_on_kernel (x : A × B)
    (hx : ComplexGaussian.LocalSectionLifting.blockDifferential a b c d x = 0) : blockSourceInclusion c d x.1 = x := by
  rw [block_source_contraction a b c d x, hx, map_zero, sub_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GaussianContraction.LocalSectionLifting
