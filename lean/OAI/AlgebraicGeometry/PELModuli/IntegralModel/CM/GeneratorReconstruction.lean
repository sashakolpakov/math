import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PrimitivePolynomialDenominators
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # Generator Reconstruction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeneratorReconstruction

noncomputable section

/-! A single primitive integral element determines every integral
endomorphism of a CM action after multiplication by one fixed integer. -/

open _root_.Polynomial

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

theorem integral_primitive_polynomial_reconstruction
    (v : NumberField.RingOfIntegers E)
    (hv : IntermediateField.adjoin ℚ {(v : E)} = ⊤) :
    ∃ (c : ℤ) (p : NumberField.RingOfIntegers E →ₗ[ℤ] ℤ[X]), c ≠ 0 ∧
      ∀ a, aeval (v : E) (p a) = (c : E) * (a : E) := by
  let b := Module.finBasis ℤ (NumberField.RingOfIntegers E)
  obtain ⟨c, P, hc, hP⟩ := PrimitivePolynomialDenominators.finite_primitive_integer_polynomial_multiples (v : E) hv
    (fun i => (b i : E))
  let p : NumberField.RingOfIntegers E →ₗ[ℤ] ℤ[X] := b.constr ℤ P
  let j : NumberField.RingOfIntegers E →ₗ[ℤ] E :=
    (algebraMap (NumberField.RingOfIntegers E) E).toIntAlgHom.toLinearMap
  have he : (aeval (v : E) : ℤ[X] →ₐ[ℤ] E).toLinearMap.comp p = c • j := by
    apply b.ext
    intro i
    change aeval (v : E) (p (b i)) = c • j (b i)
    rw [show p (b i) = P i from b.constr_basis ℤ P i]
    exact (hP i).trans (zsmul_eq_mul (b i : E) c).symm
  refine ⟨c, p, hc, ?_⟩
  intro a
  have h := LinearMap.congr_fun he a
  change aeval (v : E) (p a) = c • (a : E) at h
  exact h.trans (zsmul_eq_mul (a : E) c)

theorem integral_primitive_natural_reconstruction
    (v : NumberField.RingOfIntegers E)
    (hv : IntermediateField.adjoin ℚ {(v : E)} = ⊤) :
    ∃ (c : ℕ) (p : NumberField.RingOfIntegers E →ₗ[ℤ] ℤ[X]), c ≠ 0 ∧
      ∀ a, aeval (v : E) (p a) = (c : E) * (a : E) := by
  obtain ⟨c, p, hc, hp⟩ := integral_primitive_polynomial_reconstruction E v hv
  have hs : (c.natAbs : E) ^ 2 = (c : E) ^ 2 := by
    have h := congrArg (fun z : ℤ => (z : E)) (Int.natAbs_pow_two c)
    simpa only [Int.cast_pow, Int.cast_natCast] using h
  refine ⟨c.natAbs ^ 2, c • p, pow_ne_zero 2 (Int.natAbs_ne_zero.mpr hc), ?_⟩
  intro a
  rw [LinearMap.smul_apply, map_zsmul, hp, zsmul_eq_mul, Nat.cast_pow, hs]
  ring

structure CMIntegralGeneratorData [NumberField.IsCMField E] where
  multiplier : ℕ
  multiplier_ne_zero : multiplier ≠ 0
  generator : NumberField.RingOfIntegers E
  primitive : IntermediateField.adjoin ℚ {(generator : E)} = ⊤
  norm : generator * NumberField.IsCMField.ringOfIntegersComplexConj E generator =
    (multiplier : NumberField.RingOfIntegers E) ^ 2
  conductor : ℕ
  conductor_ne_zero : conductor ≠ 0
  polynomial : NumberField.RingOfIntegers E →ₗ[ℤ] ℤ[X]
  reconstruction : ∀ a, aeval (generator : E) (polynomial a) = (conductor : E) * (a : E)

theorem cm_integral_generator_data_exists [NumberField.IsCMField E] :
    Nonempty (CMIntegralGeneratorData E) := by
  obtain ⟨d, v, hd, hv, hnorm⟩ := Generator.cm_integral_primitive_similitude_generator E
  obtain ⟨c, p, hc, hp⟩ := integral_primitive_natural_reconstruction E v hv
  exact ⟨⟨d, hd, v, hv, hnorm, c, hc, p, hp⟩⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.CM.GeneratorReconstruction
