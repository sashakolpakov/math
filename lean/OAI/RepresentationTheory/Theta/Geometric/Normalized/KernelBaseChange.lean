import OAI.RepresentationTheory.Theta.Geometric.Normalized.RankOneKernel
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Maps

/-! # Kernel Base Change -/

namespace OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelBaseChange

noncomputable section

/-! The rank-one normalized kernel is cut out by the same original
differential coefficients after every scalar extension. -/

open scoped TensorProduct

variable {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (S : Type*) [CommRing S] [Algebra R S]

def rankOneBaseChange (e : R ≃ₗ[R] M) : S ≃ₗ[S] S ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.rid R S S).symm.trans (e.baseChange R S R M)

theorem rankOneBaseChange_one (e : R ≃ₗ[R] M) :
    rankOneBaseChange S e 1 = 1 ⊗ₜ[R] e 1 := rfl

def scalarFunctionalBaseChange (v : M →ₗ[R] R) : S ⊗[R] M →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (v.baseChange S)

theorem scalarFunctionalBaseChange_tmul (v : M →ₗ[R] R) (a : S) (m : M) :
    scalarFunctionalBaseChange S v (a ⊗ₜ[R] m) = algebraMap R S (v m) * a := by
  change v m • a = _
  exact Algebra.smul_def (v m) a

theorem normalized_rankOne_kernel_baseChange_iff
    (e : R ≃ₗ[R] M) (d : M →ₗ[R] N) (v : M →ₗ[R] R) (hv : IsUnit (v (e 1))) :
    (∃ m : S ⊗[R] M, d.baseChange S m = 0 ∧ scalarFunctionalBaseChange S v m = 1) ↔
      (1 ⊗ₜ[R] d (e 1) : S ⊗[R] N) = 0 := by
  have hv' : IsUnit (scalarFunctionalBaseChange S v (rankOneBaseChange S e 1)) := by
    rw [rankOneBaseChange_one, scalarFunctionalBaseChange_tmul, mul_one]
    exact hv.map (algebraMap R S)
  exact RankOneKernel.normalized_rankOne_kernel_iff (rankOneBaseChange S e) (d.baseChange S)
    (scalarFunctionalBaseChange S v) hv'

theorem tensor_one_eq_zero_iff_coefficients {I : Type*} (b : Module.Basis I R N) (n : N) :
    (1 ⊗ₜ[R] n : S ⊗[R] N) = 0 ↔ ∀ i, algebraMap R S (b.repr n i) = 0 := by
  constructor
  · intro h i
    have he := congrArg (fun m : S ⊗[R] N => (b.baseChange S).repr m i) h
    simpa only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
      Algebra.smul_def, mul_one] using he
  · intro h
    apply (b.baseChange S).repr.injective
    ext i
    simp only [Module.Basis.baseChange_repr_tmul, map_zero, Finsupp.zero_apply,
      Algebra.smul_def, mul_one, h]

theorem normalized_rankOne_kernel_equations {I : Type*} (b : Module.Basis I R N)
    (e : R ≃ₗ[R] M) (d : M →ₗ[R] N) (v : M →ₗ[R] R) (hv : IsUnit (v (e 1))) :
    (∃ m : S ⊗[R] M, d.baseChange S m = 0 ∧ scalarFunctionalBaseChange S v m = 1) ↔
      Ideal.span (Set.range fun i => b.repr (d (e 1)) i) ≤ RingHom.ker (algebraMap R S) := by
  rw [normalized_rankOne_kernel_baseChange_iff S e d v hv,
    tensor_one_eq_zero_iff_coefficients S b, Ideal.span_le]
  exact ⟨fun h _ ⟨i, hi⟩ => hi ▸ h i, fun h i => h ⟨i, rfl⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelBaseChange
