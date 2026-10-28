import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Kernel Dimension Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KernelDimensionCriterion

noncomputable section

/-! A specified family of cycles is a basis of a kernel exactly when
its own coefficient map is injective and the kernel has no larger dimension.
This expresses completeness as two open rank inequalities. -/
universe u v w z
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type z} [AddCommGroup N] [Module R N]

def linearKernelComparison (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0) : V →ₗ[R] d.ker :=
  s.codRestrict d.ker (fun x => LinearMap.congr_fun h x)

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {M : Type w} [AddCommGroup M] [Module K M] [FiniteDimensional K M]
variable {N : Type z} [AddCommGroup N] [Module K N]

theorem linearKernelComparison_bijective_iff (s : V →ₗ[K] M) (d : M →ₗ[K] N) (h : d.comp s = 0) :
    Function.Bijective (linearKernelComparison s d h) ↔
      Function.Injective s ∧ Module.finrank K d.ker ≤ Module.finrank K V := by
  let k := linearKernelComparison s d h
  constructor
  · intro hk
    refine ⟨fun x y hxy => hk.injective (Subtype.ext hxy), ?_⟩
    exact (LinearEquiv.ofBijective k hk).finrank_eq.ge
  · rintro ⟨hs, hd⟩
    have hk : Function.Injective k := fun x y hxy => hs (congrArg Subtype.val hxy)
    have hr : Module.finrank K V = Module.finrank K d.ker :=
      le_antisymm (LinearMap.finrank_le_finrank_of_injective hk) hd
    exact ⟨hk, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp hk⟩

theorem linearKernelComparison_bijective_iff_kernelDimensions
    (s : V →ₗ[K] M) (d : M →ₗ[K] N) (h : d.comp s = 0) :
    Function.Bijective (linearKernelComparison s d h) ↔
      Module.finrank K s.ker ≤ 0 ∧ Module.finrank K d.ker ≤ Module.finrank K V := by
  rw [linearKernelComparison_bijective_iff, Nat.le_zero, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KernelDimensionCriterion
