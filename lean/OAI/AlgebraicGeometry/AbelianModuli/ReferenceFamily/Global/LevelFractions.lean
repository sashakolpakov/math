import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.NormDenominator
import Mathlib.Tactic.FieldSimp

/-! # Level Fractions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.LevelFractions

noncomputable section

/-! One positive integer congruent to one modulo the level clears any
family of integral numerators over a common integral denominator of the
form one plus a level multiple. The result keeps the literal fractions.
-/

variable (E : Type*) [Field E] [NumberField E]

theorem integral_level_fractions_common_denominator
    {I : Type*} (ℓ : ℕ) (t : NumberField.RingOfIntegers E)
    (hx : (1 + (ℓ : NumberField.RingOfIntegers E) * t) ≠ 0)
    (F : I → NumberField.RingOfIntegers E) :
    ∃ D : ℕ, 0 < D ∧ Nat.Coprime D ℓ ∧ (ℓ : ℤ) ∣ (D : ℤ) - 1 ∧
      ∃ G : I → NumberField.RingOfIntegers E,
        ∀ i, (D : E) * ((ℓ : E) * (F i : E) / (1 + (ℓ : E) * (t : E))) =
          (ℓ : E) * (G i : E) := by
  obtain ⟨D, hD, hcoprime, hcongr, a, ha⟩ :=
    Integral.NormDenominator.integral_element_congruent_one_positive_coprime_denominator E ℓ t hx
  have hxE : (1 + (ℓ : E) * (t : E)) ≠ 0 := by
    change ((1 + (ℓ : NumberField.RingOfIntegers E) * t : NumberField.RingOfIntegers E) : E) ≠ 0
    exact fun h => hx (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)
  refine ⟨D, hD, hcoprime, hcongr, fun i => F i * a, ?_⟩
  intro i
  change (D : E) * ((ℓ : E) * (F i : E) / (1 + (ℓ : E) * (t : E))) =
    (ℓ : E) * ((F i : E) * (a : E))
  rw [← ha]
  field_simp [hxE]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.LevelFractions
