import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ComplexGaussian
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Gaussian Cokernel -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GaussianCokernel.Construction.LocalSectionLifting

noncomputable section

/-! Removing an invertible differential block preserves the cokernel. -/

universe u v₁ v₂ v₃ v₄

variable {R : Type u} [CommRing R]
    {A : Type v₁} [AddCommGroup A] [Module R A]
    {B : Type v₂} [AddCommGroup B] [Module R B]
    {C : Type v₃} [AddCommGroup C] [Module R C]
    {D : Type v₄} [AddCommGroup D] [Module R D]
    (a : A →ₗ[R] C) (b : B →ₗ[R] C) (c : A →ₗ[R] D) (d : B ≃ₗ[R] D)

def blockCokernelProjection : (C × D) →ₗ[R] C :=
  (LinearMap.fst R C D).comp (ComplexGaussian.Construction.LocalSectionLifting.blockTargetShear b d).toLinearMap

def blockCokernelToSchur : (C × D) ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d) →ₗ[R]
    C ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d) :=
  (LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d)).mapQ
    (LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d)) (blockCokernelProjection b d) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.1, (congrArg Prod.fst (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential_target_coordinates a b c d x)).symm⟩)

def schurCokernelToBlock : C ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d) →ₗ[R]
    (C × D) ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d) :=
  (LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d)).mapQ
    (LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d)) (LinearMap.inl R C D) (by
      rintro _ ⟨x, rfl⟩
      exact ⟨ComplexGaussian.Construction.LocalSectionLifting.blockSourceShear c d (x, 0), ComplexGaussian.Construction.LocalSectionLifting.blockDifferential_lift_schur a b c d x⟩)

def blockCokernelEquiv : ((C × D) ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d)) ≃ₗ[R]
    (C ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d)) :=
  LinearEquiv.ofLinearMap (blockCokernelToSchur a b c d) (schurCokernelToBlock a b c d)
    (by
      apply LinearMap.ext
      intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro x
      change (Submodule.Quotient.mk (blockCokernelProjection b d (x, 0)) :
        C ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.schurDifferential a b c d)) = Submodule.Quotient.mk x
      congr 1
      simp [blockCokernelProjection, ComplexGaussian.Construction.LocalSectionLifting.blockTargetShear])
    (by
      apply LinearMap.ext
      intro q
      refine Submodule.Quotient.induction_on _ q ?_
      intro x
      change (Submodule.Quotient.mk (blockCokernelProjection b d x, (0 : D)) :
        (C × D) ⧸ LinearMap.range (ComplexGaussian.Construction.LocalSectionLifting.blockDifferential a b c d)) = Submodule.Quotient.mk x
      apply (Submodule.Quotient.eq _).mpr
      refine ⟨(0, -d.symm x.2), ?_⟩
      apply Prod.ext
      · change a 0 + b (-d.symm x.2) = (x.1 - b (d.symm x.2)) - x.1
        simp only [map_zero, zero_add, map_neg]
        abel
      · change c 0 + d (-d.symm x.2) = 0 - x.2
        simp)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GaussianCokernel.Construction.LocalSectionLifting
