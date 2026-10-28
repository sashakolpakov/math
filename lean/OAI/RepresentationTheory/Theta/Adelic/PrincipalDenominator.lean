import OAI.RepresentationTheory.Theta.Adelic.PrincipalCoefficientOrder
import Mathlib.RingTheory.Algebraic.Integral

/-! # Principal Denominator -/

namespace OAI.RepresentationTheory.Theta.Adelic.PrincipalDenominator

noncomputable section

/-! A positive integer clears the quadratic parameter, and every
multiple of that integer also defines the required coefficient order. -/

open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

theorem exists_positive_integral_multiple (d : F) :
    ∃ N : ℕ, 0 < N ∧ ∃ q : 𝓞 F, (q : F) = (N : F) * d := by
  let : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  let : Algebra.IsAlgebraic ℤ F := Algebra.IsAlgebraic.trans ℤ ℚ F
  obtain ⟨n, hn, hi⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) d).exists_integral_multiple
  have hint : IsIntegral ℤ ((n.natAbs : F) * d) := by
    have h := hi.smul (Int.sign n)
    rw [← mul_smul, Int.sign_mul_self] at h
    simpa only [zsmul_eq_mul, Int.cast_natCast] using h
  exact ⟨n.natAbs, Int.natAbs_pos.mpr hn, ⟨_, hint⟩, rfl⟩

omit [NumberField F] in
theorem integral_multiple_of_dvd (d : F) (N M : ℕ) (q : 𝓞 F)
    (hq : (q : F) = (N : F) * d) (hNM : N ∣ M) :
    ∃ r : 𝓞 F, (r : F) = (M : F) * d := by
  obtain ⟨k, rfl⟩ := hNM
  refine ⟨k * q, ?_⟩
  simp only [map_mul, map_natCast, hq, Nat.cast_mul]
  ring

end

end OAI.RepresentationTheory.Theta.Adelic.PrincipalDenominator
