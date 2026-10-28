import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.Ideal.Maps

/-! # Section Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionCoefficientIdeal

noncomputable section

/-! A section of a projective module vanishes after arbitrary scalar
extension exactly when all of its linear coefficients vanish. These
coefficients define an actual ideal of the parameter ring. -/

open TensorProduct

universe u v w z
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
variable (A : Type w) [CommRing A] [Algebra R A]

theorem tensor_section_zero_linear_coefficient (x : M) (h : (1 : A) ⊗ₜ[R] x = 0)
    (l : M →ₗ[R] R) : algebraMap R A (l x) = 0 := by
  have he := congrArg (fun y : A ⊗[R] M => TensorProduct.rid R A (l.lTensor A y)) h
  simpa only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, map_zero,
    Algebra.smul_def, mul_one] using he

theorem tensor_section_zero_of_linear_coefficients [Module.Projective R M] (x : M)
    (h : ∀ l : M →ₗ[R] R, algebraMap R A (l x) = 0) : (1 : A) ⊗ₜ[R] x = 0 := by
  obtain ⟨s, hs⟩ := Module.Projective.out (R := R) (P := M)
  rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum, TensorProduct.tmul_sum]
  apply Finset.sum_eq_zero
  intro m hm
  have hz : algebraMap R A (s x m) = 0 := h ((Finsupp.lapply m).comp s)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
    hz, TensorProduct.zero_tmul]

theorem tensor_section_zero_iff_linear_coefficients [Module.Projective R M] (x : M) :
    (1 : A) ⊗ₜ[R] x = 0 ↔ ∀ l : M →ₗ[R] R, algebraMap R A (l x) = 0 :=
  ⟨tensor_section_zero_linear_coefficient A x, tensor_section_zero_of_linear_coefficients A x⟩

variable {ι : Type z} (x : ι → M)

def projectiveSectionCoefficientIdeal : Ideal R :=
  Ideal.span (Set.range (fun p : ι × (M →ₗ[R] R) => p.2 (x p.1)))

theorem projectiveSectionCoefficientIdeal_le_ker_iff [Module.Projective R M] :
    projectiveSectionCoefficientIdeal x ≤ RingHom.ker (algebraMap R A) ↔
      ∀ i, (1 : A) ⊗ₜ[R] x i = 0 := by
  rw [projectiveSectionCoefficientIdeal, Ideal.span_le]
  constructor
  · intro h i
    apply tensor_section_zero_of_linear_coefficients A (x i)
    intro l
    exact h ⟨(i, l), rfl⟩
  · intro h r hr
    obtain ⟨⟨i, l⟩, rfl⟩ := hr
    exact tensor_section_zero_linear_coefficient A (x i) (h i) l

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionCoefficientIdeal
