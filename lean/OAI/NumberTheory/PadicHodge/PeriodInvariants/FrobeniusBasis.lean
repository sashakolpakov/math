import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Frobenius Basis -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusBasis

noncomputable section

/-! # The linear map determined by p-th powers of a basis -/

open scoped TensorProduct

variable (p : ℕ) {R S ι : Type*} [CommRing R] [CommRing S]
  [Algebra R S] (b : Module.Basis ι R S)

def linear : S →ₗ[R] S := b.constr R (fun i => b i ^ p)

theorem linear_basis (i : ι) : linear p b (b i) = b i ^ p := b.constr_basis R _ i

variable [Fact p.Prime] [CharP S p] [Fintype ι]

theorem power_sum (c : ι → R) :
    (∑ i, c i • b i) ^ p = ∑ i, c i ^ p • b i ^ p := by
  change frobenius S p (∑ i, c i • b i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (c i • b i) ^ p = _
  simp only [Algebra.smul_def, mul_pow, map_pow]

theorem power_mem_range (x : S) : x ^ p ∈ LinearMap.range (linear p b) := by
  refine ⟨∑ i, b.repr x i ^ p • b i, ?_⟩
  rw [map_sum]
  simp only [map_smul, linear_basis]
  rw [← power_sum, b.sum_repr]

theorem surjective_of_perfect [PerfectRing S p] : Function.Surjective (linear p b) := by
  intro x
  obtain ⟨y, hy⟩ := surjective_frobenius S p x
  exact hy ▸ power_mem_range p b y

theorem frobenius_surjective [CharP R p] [PerfectRing R p]
    (h : Function.Surjective (linear p b)) :
    Function.Surjective (frobenius S p) := by
  intro x
  obtain ⟨y, rfl⟩ := h x
  refine ⟨∑ i, (frobeniusEquiv R p).symm (b.repr y i) • b i, ?_⟩
  change (∑ i, (frobeniusEquiv R p).symm (b.repr y i) • b i) ^ p = _
  rw [power_sum]
  simp only [frobeniusEquiv_symm_pow_p]
  exact (Module.Basis.constr_apply_fintype R b (fun i => b i ^ p) y).symm

variable (T : Type*) [CommRing T] [Algebra R T]

omit [Fact p.Prime] [CharP S p] [Fintype ι] in
theorem baseChange : (linear p b).baseChange T = linear p (b.baseChange T) := by
  apply (b.baseChange T).ext
  intro i
  rw [linear_basis, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    linear_basis, Algebra.TensorProduct.tmul_pow, one_pow]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.FrobeniusBasis
