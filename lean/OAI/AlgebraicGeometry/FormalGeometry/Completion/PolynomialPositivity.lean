import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! # Polynomial Positivity -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity.Construction

noncomputable section

/-! Eventual nonnegative section dimensions force nonnegative leading
coefficients, and a nonzero Hilbert polynomial has positive leading coefficient. -/

open Filter

theorem polynomial_leadingCoeff_nonneg_of_eventual_nat_nonneg
    (P : Polynomial ℚ) (b : ℕ) (h : ∀ n : ℕ, b ≤ n → 0 ≤ P.eval (n : ℚ)) :
    0 ≤ P.leadingCoeff := by
  by_cases hdeg : P.degree ≤ 0
  · have he := Polynomial.eq_C_of_degree_le_zero hdeg
    have hb := h b le_rfl
    rw [he] at hb ⊢
    simpa only [Polynomial.eval_C, Polynomial.leadingCoeff_C] using hb
  · by_contra hlc
    have ht : Tendsto (fun n : ℕ => P.eval (n : ℚ)) atTop atBot :=
      (P.tendsto_atBot_of_leadingCoeff_nonpos (lt_of_not_ge hdeg)
        (le_of_lt (lt_of_not_ge hlc))).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hnb⟩ := ((ht.eventually (eventually_lt_atBot (0 : ℚ))).and
      (eventually_ge_atTop b)).exists
    exact (not_lt_of_ge (h n hnb)) hn

theorem polynomial_leadingCoeff_pos_of_eventual_nat_nonneg
    (P : Polynomial ℚ) (hP : P ≠ 0) (b : ℕ)
    (h : ∀ n : ℕ, b ≤ n → 0 ≤ P.eval (n : ℚ)) : 0 < P.leadingCoeff := by
  rcases eq_or_lt_of_le (polynomial_leadingCoeff_nonneg_of_eventual_nat_nonneg P b h) with he | he
  · exact False.elim (hP (Polynomial.leadingCoeff_eq_zero.mp he.symm))
  · exact he

theorem polynomial_eventually_nat_pos_of_leadingCoeff_pos
    (P : Polynomial ℚ) (hP : 0 < P.leadingCoeff) :
    ∃ b : ℕ, ∀ n : ℕ, b ≤ n → 0 < P.eval (n : ℚ) := by
  by_cases hdeg : P.degree ≤ 0
  · have he : P = Polynomial.C P.leadingCoeff := by
      simpa only [← Polynomial.coeff_natDegree,
        Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hdeg] using
        Polynomial.eq_C_of_degree_le_zero hdeg
    refine ⟨0, fun n _ => ?_⟩
    rw [he, Polynomial.eval_C]
    exact hP
  · have ht := (P.tendsto_atTop_of_leadingCoeff_nonneg (lt_of_not_ge hdeg) hP.le).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))
    exact Filter.eventually_atTop.mp (ht.eventually_gt_atTop 0)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity.Construction
