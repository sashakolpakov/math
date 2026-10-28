import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot

/-! # Quotient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Quotient.Integral

noncomputable section

/-! A rational function which takes integer values at every sufficiently
large integer has no proper rational-function part. This lets geometric
divisibility of degrees imply divisibility of rational polynomials. -/

open Filter _root_.Polynomial
open scoped _root_.Topology

theorem eq_zero_of_degree_lt_of_integral_quotient
    (R P : Polynomial ℚ) (hdeg : R.degree < P.degree)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, R.eval (n : ℚ) = P.eval (n : ℚ) * z) :
    R = 0 := by
  have hP : P ≠ 0 := by
    intro he
    simp only [he, Polynomial.degree_zero] at hdeg
    exact not_lt_bot hdeg
  have hlim : Tendsto (fun n : ℕ => R.eval (n : ℚ) / P.eval (n : ℚ)) atTop (𝓝 0) :=
    (R.div_tendsto_atTop_zero_of_degree_lt P hdeg).comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      R.eval (n : ℚ) / P.eval (n : ℚ) ∈ Set.Ioo (-1 : ℚ) 1 :=
    hlim.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hne : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) ≠ 0 :=
    tendsto_natCast_atTop_atTop.eventually (P.eventually_atTop_not_isRoot hP)
  have hz : ∀ᶠ n : ℕ in atTop, R.eval (n : ℚ) = 0 := by
    filter_upwards [h, hsmall, hne] with n hn hs hp
    obtain ⟨z, hz⟩ := hn
    have hquot : R.eval (n : ℚ) / P.eval (n : ℚ) = (z : ℚ) := by
      rw [hz, mul_div_cancel_left₀ _ hp]
    rw [hquot] at hs
    have hlo : (-1 : ℤ) < z := by exact_mod_cast hs.1
    have hhi : z < (1 : ℤ) := by exact_mod_cast hs.2
    have hzero : z = 0 := by omega
    simpa only [hzero, Int.cast_zero, mul_zero] using hz
  obtain ⟨b, hb⟩ := eventually_atTop.mp hz
  exact AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity.Dimension.polynomial_eq_of_eventually_nat_eval_eq R 0 b
    (fun n hn => by simpa only [Polynomial.eval_zero] using hb n hn)

theorem dvd_of_eventual_integral_quotient
    (P Q : Polynomial ℚ) (hP : P ≠ 0)
    (h : ∀ᶠ n : ℕ in atTop, ∃ z : ℤ, Q.eval (n : ℚ) = P.eval (n : ℚ) * z) :
    P ∣ Q := by
  let S := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (Q / P)
  obtain ⟨k, hk, he⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors ℤ) (Q / P)
  have hk0 : k ≠ 0 := nonZeroDivisors.ne_zero hk
  have hkQ : (k : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hk0
  have hS (n : ℕ) : ((S.eval (n : ℤ) : ℤ) : ℚ) = (k : ℚ) * (Q / P).eval (n : ℚ) := by
    have hv := congrArg (fun T : Polynomial ℚ => T.eval (n : ℚ)) he
    simpa only [S, Polynomial.eval_natCast_map, Polynomial.eval_smul,
      zsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_intCast,
      algebraMap_int_eq, Int.coe_castRingHom, Int.cast_natCast] using hv
  let R := Polynomial.C (k : ℚ) * (Q % P)
  have hdeg : R.degree < P.degree := by
    change (Polynomial.C (k : ℚ) * (Q % P)).degree < P.degree
    rw [Polynomial.degree_C_mul hkQ]
    exact Polynomial.degree_mod_lt Q hP
  have hR : R = 0 := eq_zero_of_degree_lt_of_integral_quotient R P hdeg (by
    filter_upwards [h] with n hn
    obtain ⟨z, hz⟩ := hn
    refine ⟨k * z - S.eval (n : ℤ), ?_⟩
    change (Polynomial.C (k : ℚ) * (Q % P)).eval (n : ℚ) = _
    rw [EuclideanDomain.mod_eq_sub_mul_div, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_mul, hz, Int.cast_sub, Int.cast_mul, hS]
    ring)
  have hmod : Q % P = 0 := (mul_eq_zero.mp hR).resolve_left (by simpa using hkQ)
  exact EuclideanDomain.mod_eq_zero.mp hmod

theorem exists_monic_integer_of_dvd_monic
    (P : Polynomial ℚ) (hP : P.Monic)
    (Q : Polynomial ℤ) (hQ : Q.Monic)
    (h : P ∣ Q.map (Int.castRingHom ℚ)) :
    ∃ R : Polynomial ℤ, R.Monic ∧ R.map (Int.castRingHom ℚ) = P := by
  have hi (i : ℕ) : IsIntegral ℤ (P.coeff i) :=
    Polynomial.isIntegral_coeff_of_dvd Q P hQ hP h i
  have hlift : P ∈ Polynomial.lifts (Int.castRingHom ℚ) := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro i
    exact IsIntegrallyClosed.algebraMap_eq_of_integral (hi i)
  obtain ⟨R, hR⟩ := Polynomial.mem_lifts P |>.mp hlift
  refine ⟨R, ?_, hR⟩
  exact Polynomial.monic_of_injective (Int.cast_injective (α := ℚ)) (hR ▸ hP)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Quotient.Integral
