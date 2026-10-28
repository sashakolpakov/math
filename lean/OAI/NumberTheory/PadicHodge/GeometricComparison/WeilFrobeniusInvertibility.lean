import OAI.NumberTheory.PadicHodge.GeometricComparison.WeilDeterminantNorm
import Mathlib.LinearAlgebra.Determinant

/-! # Weil Frobenius Invertibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.WeilFrobeniusInvertibility.WeilDeterminant

noncomputable section

/-! A characteristic polynomial whose complex roots have positive Weil
weight has nonzero constant coefficient, so its operator is invertible. -/

variable (q : ℕ) [Fact q.Prime]
  {V : Type*} [AddCommGroup V] [Module ℚ_[q] V] [FiniteDimensional ℚ_[q] V]

theorem determinant_ne_zero (F : Module.End ℚ_[q] V) (P : Polynomial ℤ)
    (hP : F.charpoly = P.map (Int.castRingHom ℚ_[q]))
    (h : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ = Real.sqrt (q : ℝ)) :
    F.det ≠ 0 := by
  have hm : P.Monic := Polynomial.monic_of_injective
    (show Function.Injective (Int.castRingHom ℚ_[q]) from Int.cast_injective)
    (hP ▸ F.charpoly_monic)
  have hc : P.coeff 0 ≠ 0 := by
    intro hzero
    have heq := WeilDeterminantNorm.WeilDeterminant.constant_square q P hm h
    rw [hzero, zero_pow (by decide)] at heq
    have hq : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    exact (pow_ne_zero P.natDegree hq) heq.symm
  rw [LinearMap.det_eq_sign_charpoly_coeff, hP, Polynomial.coeff_map]
  apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  change (P.coeff 0 : ℚ_[q]) ≠ 0
  exact_mod_cast hc

theorem bijective (F : Module.End ℚ_[q] V) (P : Polynomial ℤ)
    (hP : F.charpoly = P.map (Int.castRingHom ℚ_[q]))
    (h : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ = Real.sqrt (q : ℝ)) :
    Function.Bijective F :=
  (Module.End.isUnit_iff F).mp ((LinearMap.isUnit_iff_isUnit_det F).mpr
    (isUnit_iff_ne_zero.mpr (determinant_ne_zero q F P hP h)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.WeilFrobeniusInvertibility.WeilDeterminant
