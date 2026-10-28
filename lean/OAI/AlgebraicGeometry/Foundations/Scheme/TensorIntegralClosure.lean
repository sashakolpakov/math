import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Tensor Integral Closure -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.TensorIntegralClosure

noncomputable section

/-!
# Integral elements in a tensor product over an integrally closed domain

If the canonical integral-closure base-change map is surjective, every
integral element in the generic fiber comes from the original algebra.
Flatness then identifies that algebra with an integrally closed subring of
its generic fiber. These are consequences of the actual comparison map,
not additional normality assumptions on the algebra.
-/

open scoped TensorProduct

variable {R A K : Type*} [CommRing R] [IsIntegrallyClosed R]
variable [CommRing A] [Algebra R A]
variable [Field K] [Algebra R K] [IsFractionRing R K]

/-- Surjectivity of the integral-closure comparison puts every integral
generic-fiber element in the image of the original algebra. -/
theorem exists_tensorLeft_eq_of_isIntegral
    (h : Function.Surjective (TensorProduct.toIntegralClosure R A K))
    (z : A ⊗[R] K) (hz : IsIntegral A z) :
    ∃ a : A, algebraMap A (A ⊗[R] K) a = z := by
  obtain ⟨y, hy⟩ := h ⟨z, hz⟩
  have lift (y : A ⊗[R] integralClosure R K) :
      ∃ a : A, algebraMap A (A ⊗[R] K) a =
        (TensorProduct.toIntegralClosure R A K y).val := by
    induction y with
    | add y₁ y₂ hy₁ hy₂ =>
        obtain ⟨a₁, ha₁⟩ := hy₁
        obtain ⟨a₂, ha₂⟩ := hy₂
        exact ⟨a₁ + a₂, by simp only [map_add, Subalgebra.coe_add, ha₁, ha₂]⟩
    | tmul a b =>
        obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp b.property
        refine ⟨r • a, ?_⟩
        change (r • a) ⊗ₜ[R] (1 : K) = a ⊗ₜ[R] b.val
        rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
  obtain ⟨a, ha⟩ := lift y
  exact ⟨a, ha.trans (congrArg Subtype.val hy)⟩

/-- With flatness, the original algebra is integrally closed in its generic
fiber whenever the actual integral-closure comparison is surjective. -/
theorem isIntegrallyClosedIn_tensor_of_comparison_surjective [Module.Flat R A]
    (h : Function.Surjective (TensorProduct.toIntegralClosure R A K)) :
    IsIntegrallyClosedIn A (A ⊗[R] K) := by
  apply isIntegrallyClosedIn_iff.mpr
  refine ⟨?_, fun {z} hz => exists_tensorLeft_eq_of_isIntegral h z hz⟩
  exact Algebra.TensorProduct.includeLeft_injective (S := A) (IsFractionRing.injective R K)

/-- A smooth algebra over an integrally closed domain is integrally closed
inside the actual generic fiber. -/
theorem smooth_isIntegrallyClosedIn_genericFiber [Algebra.Smooth R A] :
    IsIntegrallyClosedIn A (A ⊗[R] K) :=
  isIntegrallyClosedIn_tensor_of_comparison_surjective
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := A) (B := K)).surjective

end

end OAI.AlgebraicGeometry.Foundations.Scheme.TensorIntegralClosure
