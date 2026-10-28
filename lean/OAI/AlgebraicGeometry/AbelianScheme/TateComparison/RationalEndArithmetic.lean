import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.EndTorsionFree
import Mathlib.RingTheory.Localization.BaseChange

/-! # Rational End Arithmetic -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalEndArithmetic

noncomputable section

/-! Rational algebraic endomorphisms admit actual positive integer
denominator clearings. Torsion-freeness makes the integral inclusion faithful. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct _root_.CategoryTheory.MonObj

theorem rationalTensor_positive_denominator (M : Type*) [AddCommGroup M]
    (x : ℚ ⊗[ℤ] M) : ∃ (n : ℕ), 0 < n ∧ ∃ a : M, n • x = 1 ⊗ₜ[ℤ] a := by
  let f := TensorProduct.mk ℤ ℚ M 1
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f x
  have hm0 : (m : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m.property
  refine ⟨(m : ℤ).natAbs ^ 2, pow_pos (Int.natAbs_pos.mpr hm0) _, (m : ℤ) • a, ?_⟩
  change _ = f ((m : ℤ) • a)
  change (m : ℤ) • x = f a at hm
  rw [f.map_smul, ← hm]
  change _ = (m : ℤ) • ((m : ℤ) • x)
  rw [← mul_smul]
  have he : (((m : ℤ).natAbs ^ 2 : ℕ) : ℤ) = (m : ℤ) * (m : ℤ) := by
    rw [Nat.cast_pow, Int.natCast_natAbs, sq_abs, pow_two]
  rw [← he]
  exact (Nat.cast_smul_eq_nsmul ℤ _ x).symm

theorem rationalTensor_one_injective (M : Type*) [AddCommGroup M]
    [IsAddTorsionFree M] : Function.Injective (TensorProduct.mk ℤ ℚ M 1) := by
  intro a b hab
  obtain ⟨m, hm⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors ℤ)
    (f := TensorProduct.mk ℤ ℚ M 1) hab
  have hm0 : (m : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp m.property
  change (m : ℤ) • a = (m : ℤ) • b at hm
  exact zsmul_right_injective hm0 hm

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]

theorem rationalEnd_positive_denominator (x : End.RationalEnd A) :
    ∃ (n : ℕ), 0 < n ∧ ∃ a : End.IntegralEnd A, n • x = End.endToRational A a :=
  rationalTensor_positive_denominator (End.IntegralEnd A) x

theorem endToRational_injective [IsAddTorsionFree (End.IntegralEnd A)] :
    Function.Injective (End.endToRational A) := rationalTensor_one_injective (End.IntegralEnd A)

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalEndArithmetic
