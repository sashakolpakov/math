import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Differential Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoefficientIdeal

noncomputable section

/-! The ideal of coefficients of an actual linear differential represents precisely the base changes on which that differential becomes zero. It is independent of the two chosen bases. -/
open _root_.Module
open scoped TensorProduct
universe u

variable {R M N : Type u} [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable {ι κ : Type u} (b : Basis ι R M) (c : Basis κ R N) (f : M →ₗ[R] N)

def differentialCoefficientIdeal : Ideal R :=
  Ideal.span (Set.range fun p : ι × κ => c.repr (f (b p.1)) p.2)

theorem differential_baseChange_zero_iff_coefficients
    (B : Type u) [CommRing B] [Algebra R B] :
    f.baseChange B = 0 ↔ differentialCoefficientIdeal b c f ≤ RingHom.ker (algebraMap R B) := by
  constructor
  · intro hf
    apply Ideal.span_le.mpr
    rintro r ⟨⟨i, j⟩, rfl⟩
    change algebraMap R B (c.repr (f (b i)) j) = 0
    have h := congrArg (fun z : B ⊗[R] M →ₗ[B] B ⊗[R] N =>
      (c.baseChange B).repr (z (1 ⊗ₜ[R] b i)) j) hf
    simpa only [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      LinearMap.zero_apply, map_zero, Finsupp.zero_apply, Algebra.smul_def, mul_one] using h
  · intro hf
    apply (b.baseChange B).ext
    intro i
    apply (c.baseChange B).repr.injective
    ext j
    have h : algebraMap R B (c.repr (f (b i)) j) = 0 :=
      hf (Ideal.subset_span ⟨(i, j), rfl⟩)
    simpa only [Basis.baseChange_apply, LinearMap.baseChange_tmul,
      Basis.baseChange_repr_tmul, LinearMap.zero_apply, map_zero,
      Finsupp.zero_apply, Algebra.smul_def, mul_one] using h

theorem differential_coefficients_le_iff_quotient_zero (J : Ideal R) :
    differentialCoefficientIdeal b c f ≤ J ↔ f.baseChange (R ⧸ J) = 0 := by
  rw [differential_baseChange_zero_iff_coefficients b c f]
  constructor
  · intro h x hx
    change Ideal.Quotient.mk J x = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h hx)
  · intro h x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (h hx)

theorem differential_coefficient_quotient_zero :
    f.baseChange (R ⧸ differentialCoefficientIdeal b c f) = 0 :=
  (differential_coefficients_le_iff_quotient_zero b c f _).mp le_rfl

theorem differentialCoefficientIdeal_basis_independent
    {ι' κ' : Type u} (b' : Basis ι' R M) (c' : Basis κ' R N) :
    differentialCoefficientIdeal b c f = differentialCoefficientIdeal b' c' f := by
  apply le_antisymm
  · exact (differential_coefficients_le_iff_quotient_zero b c f _).mpr
      (differential_coefficient_quotient_zero b' c' f)
  · exact (differential_coefficients_le_iff_quotient_zero b' c' f _).mpr
      (differential_coefficient_quotient_zero b c f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DifferentialCoefficientIdeal
