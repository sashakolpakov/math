import OAI.AlgebraicGeometry.ComplexMultiplication.CM.Polarization
import Mathlib.RingTheory.Localization.Integral

/-! # Integral Polarization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# Clearing the denominators of the CM polarization

A positive integer multiple of the chosen imaginary element is an
algebraic integer. Its trace pairing is integer-valued on the ring of
integers. Positive rational scaling preserves the polarization conditions,
so this gives an integral pairing on the full arithmetic lattice.
The embedding of that lattice as a discrete cocompact subgroup is separate.
-/

open scoped TensorProduct Classical _root_.NumberField

variable {U : Type*} [AddCommGroup U] [Module ℚ U]

/-- Scalar extension of a rational bilinear form respects rational scaling. -/
theorem IntegralPolarization.bilinForm_baseChange_smul (q : ℚ) (B : LinearMap.BilinForm ℚ U)
    (u v : WeightOne.CM.Complexification U) :
    (q • B).baseChange ℂ u v = q • B.baseChange ℂ u v := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw, smul_add]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]
    | tmul b y => simp [smul_smul]

section

variable {H : WeightOne.CM.WeightOneHodgeStructure U} (P : Polarization.WeightOnePolarization H)

/-- Scaling by a positive rational number preserves a weight-one polarization. -/
def Polarization.WeightOnePolarization.positiveScale (q : ℚ) (hq : 0 < q) : Polarization.WeightOnePolarization H where
  form := q • P.form
  alternating x := by change q * P.form x x = 0; rw [P.alternating x, mul_zero]
  nondegenerate := by
    constructor
    · intro x hx
      apply P.nondegenerate.1 x
      intro y
      exact (mul_eq_zero.mp (hx y)).resolve_left hq.ne'
    · intro y hy
      apply P.nondegenerate.2 y
      intro x
      exact (mul_eq_zero.mp (hy x)).resolve_left hq.ne'
  holomorphic_isotropic u hu v hv := by
    rw [IntegralPolarization.bilinForm_baseChange_smul, P.holomorphic_isotropic u hu v hv, smul_zero]
  hodge_self_real u := by
    rw [IntegralPolarization.bilinForm_baseChange_smul, mul_smul_comm, Complex.im_qsmul,
      P.hodge_self_real, smul_zero]
  hodge_positive u hu hne := by
    rw [IntegralPolarization.bilinForm_baseChange_smul, mul_smul_comm, Complex.re_qsmul, Rat.smul_def]
    exact mul_pos (by exact_mod_cast hq) (P.hodge_positive u hu hne)

end

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

omit [NumberField.IsCMField E] in
/-- A nonzero natural multiple of a number-field element lies in its ring of integers. -/
theorem IntegralPolarization.exists_positive_integral_multiple (x : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ (n • x) := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (.of_finite ℚ x)
  obtain ⟨n, a, hn, ha⟩ := hx.exists_nsmul_eq (𝓞 E)
  refine ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  rw [ha]
  exact a.property

/-- The trace pairing depends rationally linearly on its imaginary coefficient. -/
theorem IntegralPolarization.cmTracePairing_nsmul (n : ℕ) (ξ : E) :
    TraceForm.cmTracePairing E (n • ξ) = (n : ℚ) • TraceForm.cmTracePairing E ξ := by
  ext x y
  rw [TraceForm.cmTracePairing_apply, smul_mul_assoc, smul_mul_assoc, map_nsmul]
  simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, TraceForm.cmTracePairing_apply]

/-- An integral imaginary coefficient gives integer values on pairs of algebraic integers. -/
theorem IntegralPolarization.cmTracePairing_isInteger (ξ : E) (hξ : IsIntegral ℤ ξ) (x y : 𝓞 E) :
    ∃ z : ℤ, (z : ℚ) = TraceForm.cmTracePairing E ξ (x : E) (y : E) := by
  have hc : IsIntegral ℤ (TraceForm.cmFieldConjugation E (x : E)) :=
    map_isIntegral_int (TraceForm.cmFieldConjugation E).toRingHom x.property
  have ht : IsIntegral ℤ (TraceForm.cmTracePairing E ξ (x : E) (y : E)) :=
    Algebra.isIntegral_trace ((hξ.mul hc).mul y.property)
  exact IsIntegrallyClosed.isIntegral_iff.mp ht

variable {E} (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- A positive multiplier clearing the denominator of the CM imaginary element. -/
def TypeHodgeStructure.CMEmbeddingType.polarizationMultiplier : ℕ := (IntegralPolarization.exists_positive_integral_multiple E ε.imaginaryElement).choose

theorem TypeHodgeStructure.CMEmbeddingType.polarizationMultiplier_pos : 0 < ε.polarizationMultiplier :=
  (IntegralPolarization.exists_positive_integral_multiple E ε.imaginaryElement).choose_spec.1

theorem TypeHodgeStructure.CMEmbeddingType.polarizationMultiplier_integral : IsIntegral ℤ (ε.polarizationMultiplier • ε.imaginaryElement) :=
  (IntegralPolarization.exists_positive_integral_multiple E ε.imaginaryElement).choose_spec.2

/-- A polarization whose rational form is integral on the ring of integers. -/
def TypeHodgeStructure.CMEmbeddingType.integralPolarization : Polarization.WeightOnePolarization ε.hodgeStructure :=
  ε.polarization.positiveScale (ε.polarizationMultiplier : ℚ)
    (by exact_mod_cast ε.polarizationMultiplier_pos)

theorem TypeHodgeStructure.CMEmbeddingType.integralPolarization_form : ε.integralPolarization.form =
    TraceForm.cmTracePairing E (ε.polarizationMultiplier • ε.imaginaryElement) :=
  (IntegralPolarization.cmTracePairing_nsmul E ε.polarizationMultiplier ε.imaginaryElement).symm

theorem TypeHodgeStructure.CMEmbeddingType.integralPolarization_isInteger (x y : 𝓞 E) :
    ∃ z : ℤ, (z : ℚ) = ε.integralPolarization.form (x : E) (y : E) := by
  rw [ε.integralPolarization_form]
  exact IntegralPolarization.cmTracePairing_isInteger E _ ε.polarizationMultiplier_integral x y

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
