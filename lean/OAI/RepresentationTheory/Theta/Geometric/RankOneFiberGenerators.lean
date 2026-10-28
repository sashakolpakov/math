import OAI.RepresentationTheory.Theta.Geometric.Normalized.KernelBaseChange
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Rank One Fiber Generators -/

namespace OAI.RepresentationTheory.Theta.Geometric.RankOneFiberGenerators

noncomputable section

/-! Nonvanishing in every residue-field fiber makes a section of a
rank-one free module a generator, and its cycle equation kills the
original differential coefficients without discarding nilpotents. -/

open scoped TensorProduct

variable {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem rankOne_coordinate_isUnit_of_fibers (e : R ≃ₗ[R] M) (m : M)
    (hm : ∀ (I : Ideal R) [I.IsMaximal], (1 ⊗ₜ[R] m : (R ⧸ I) ⊗[R] M) ≠ 0) :
    IsUnit (e.symm m) := by
  by_contra h
  obtain ⟨I, hI, hi⟩ := exists_max_ideal_of_mem_nonunits h
  let : I.IsMaximal := hI
  apply hm I
  have hq : algebraMap R (R ⧸ I) (e.symm m) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hi
  calc
    (1 ⊗ₜ[R] m : (R ⧸ I) ⊗[R] M) = 1 ⊗ₜ[R] (e.symm m • e 1) := by
      exact congrArg (fun z : M => (1 : R ⧸ I) ⊗ₜ[R] z)
        ((e.apply_symm_apply m).symm.trans (Normalized.RankOneKernel.rankOne_apply e (e.symm m)))
    _ = (e.symm m • (1 : R ⧸ I)) ⊗ₜ[R] e 1 := TensorProduct.tmul_smul _ _ _
    _ = 0 := by rw [Algebra.smul_def, hq, zero_mul, TensorProduct.zero_tmul]

theorem rankOne_differential_zero_of_unit_coordinate (e : R ≃ₗ[R] M)
    (d : M →ₗ[R] N) (m : M) (hd : d m = 0) (hu : IsUnit (e.symm m)) :
    d (e 1) = 0 := by
  have he : e.symm m • d (e 1) = 0 := by
    rw [← map_smul, ← Normalized.RankOneKernel.rankOne_apply, e.apply_symm_apply, hd]
  exact hu.smul_eq_zero.mp he

theorem rankOne_differential_zero_of_fiber_generator (e : R ≃ₗ[R] M)
    (d : M →ₗ[R] N) (m : M) (hd : d m = 0)
    (hm : ∀ (I : Ideal R) [I.IsMaximal], (1 ⊗ₜ[R] m : (R ⧸ I) ⊗[R] M) ≠ 0) :
    d (e 1) = 0 :=
  rankOne_differential_zero_of_unit_coordinate e d m hd
    (rankOne_coordinate_isUnit_of_fibers e m hm)

theorem rankOne_generator_cycle_iff (e : R ≃ₗ[R] M) (d : M →ₗ[R] N) :
    (∃ m : M, d m = 0 ∧ IsUnit (e.symm m)) ↔ d (e 1) = 0 := by
  constructor
  · rintro ⟨m, hd, hu⟩
    exact rankOne_differential_zero_of_unit_coordinate e d m hd hu
  · intro hd
    refine ⟨e 1, hd, ?_⟩
    rw [e.symm_apply_apply]
    exact isUnit_one

theorem rankOne_generator_cycle_equations
    (T : Type*) [CommRing T] [Algebra R T] {I : Type*} (b : Module.Basis I R N)
    (e : R ≃ₗ[R] M) (d : M →ₗ[R] N) :
    (∃ m : T ⊗[R] M, d.baseChange T m = 0 ∧
      IsUnit ((Normalized.KernelBaseChange.rankOneBaseChange T e).symm m)) ↔
    Ideal.span (Set.range fun i => b.repr (d (e 1)) i) ≤ RingHom.ker (algebraMap R T) := by
  rw [rankOne_generator_cycle_iff]
  change (1 ⊗ₜ[R] d (e 1) : T ⊗[R] N) = 0 ↔ _
  rw [Normalized.KernelBaseChange.tensor_one_eq_zero_iff_coefficients T b, Ideal.span_le]
  exact ⟨fun h _ ⟨i, hi⟩ => hi ▸ h i, fun h i => h ⟨i, rfl⟩⟩

end

end OAI.RepresentationTheory.Theta.Geometric.RankOneFiberGenerators
