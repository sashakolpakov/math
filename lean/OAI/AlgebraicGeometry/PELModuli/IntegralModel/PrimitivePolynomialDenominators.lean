import OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.Generator
import Mathlib.RingTheory.Localization.Integral

/-! # Primitive Polynomial Denominators -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimitivePolynomialDenominators

noncomputable section

/-! Recover any finite collection of field elements by integral
polynomials in a primitive generator, with one nonzero integer multiplier. -/

open _root_.Polynomial IntermediateField
open scoped nonZeroDivisors BigOperators

variable {E : Type*} [Field E] [Algebra ℚ E] [Algebra.IsAlgebraic ℚ E]

theorem primitive_integer_polynomial_multiple (v : E)
    (hv : IntermediateField.adjoin ℚ {v} = ⊤) (z : E) :
    ∃ (c : ℤ) (p : ℤ[X]), c ≠ 0 ∧ aeval v p = (c : E) * z := by
  have hA : Algebra.adjoin ℚ {v} = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff).mp hv
  have hs : Function.Surjective (aeval v : ℚ[X] →ₐ[ℚ] E) := by
    apply (AlgHom.range_eq_top _).mp
    exact (Algebra.adjoin_singleton_eq_range_aeval ℚ v).symm.trans hA
  obtain ⟨q, hq⟩ := hs z
  obtain ⟨c, hc, hcp⟩ := IsLocalization.integerNormalization_spec ℤ⁰ q
  let p := IsLocalization.integerNormalization ℤ⁰ q
  have he : (aeval v : ℚ[X] →ₐ[ℚ] E) (p.map (algebraMap ℤ ℚ)) = (c : E) * z := by
    rw [hcp, map_zsmul, hq, zsmul_eq_mul]
  exact ⟨c, p, mem_nonZeroDivisors_iff_ne_zero.mp hc,
    (aeval_eq_aeval_map (φ := algebraMap ℤ ℚ) (Subsingleton.elim _ _) p v).trans he⟩

theorem finite_primitive_integer_polynomial_multiples
    {ι : Type*} [Fintype ι] (v : E) (hv : IntermediateField.adjoin ℚ {v} = ⊤)
    (z : ι → E) :
    ∃ (c : ℤ) (p : ι → ℤ[X]), c ≠ 0 ∧ ∀ i, aeval v (p i) = (c : E) * z i := by
  choose c p hc hp using fun i => primitive_integer_polynomial_multiple v hv (z i)
  let C : ℤ := ∏ i, c i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hc i)
  have hdiv (i : ι) : c i ∣ C := Finset.dvd_prod_of_mem c (Finset.mem_univ i)
  choose k hk using hdiv
  refine ⟨C, (fun i => Polynomial.C (k i) * p i), hC, ?_⟩
  intro i
  rw [map_mul, aeval_C, hp]
  have he : (C : E) = (c i : E) * (k i : E) :=
    (congrArg (fun z : ℤ => (z : E)) (hk i)).trans (Int.cast_mul _ _)
  rw [he]
  have hz : algebraMap ℤ E (k i) = (k i : E) := map_intCast (algebraMap ℤ E) (k i)
  rw [hz]
  ring

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimitivePolynomialDenominators
