import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Split Kernel Augmentation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SplitKernelAugmentation

noncomputable section

/-! A split kernel contained in an ideal multiple equals its own ideal multiple. -/

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

def splitKernelRetraction (p : M →ₗ[R] N) (s : N →ₗ[R] M)
    (h : p.comp s = LinearMap.id) : M →ₗ[R] p.ker :=
  (LinearMap.id - s.comp p).codRestrict p.ker (by
    intro x
    change p (x - s (p x)) = 0
    rw [map_sub]
    have hx := LinearMap.congr_fun h (p x)
    change p (s (p x)) = p x at hx
    rw [hx, sub_self])

theorem splitKernelRetraction_apply (p : M →ₗ[R] N) (s : N →ₗ[R] M)
    (h : p.comp s = LinearMap.id) (x : p.ker) : splitKernelRetraction p s h x.val = x := by
  apply Subtype.ext
  change x.val - s (p x.val) = x.val
  rw [x.property, map_zero, sub_zero]

theorem splitKernel_le_ideal_smul_top (p : M →ₗ[R] N) (s : N →ₗ[R] M)
    (h : p.comp s = LinearMap.id) (I : Ideal R)
    (hker : p.ker ≤ I • ⊤) : (⊤ : Submodule R p.ker) ≤ I • ⊤ := by
  intro x _
  have hx := Submodule.smul_top_le_comap_smul_top I (splitKernelRetraction p s h)
    (hker x.property)
  change splitKernelRetraction p s h x.val ∈ I • (⊤ : Submodule R p.ker) at hx
  rwa [splitKernelRetraction_apply] at hx

theorem finsupp_mem_ideal_smul_top {ι : Type*} (I : Ideal R) (x : ι →₀ R)
    (hx : ∀ i, x i ∈ I) : x ∈ I • (⊤ : Submodule R (ι →₀ R)) := by
  classical
  rw [← x.sum_single]
  apply Submodule.sum_mem
  intro i _
  rw [← Finsupp.smul_single_one]
  exact Submodule.smul_mem_smul (hx i) (by trivial)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SplitKernelAugmentation
