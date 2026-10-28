import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Rat

/-! # Polynomial Growth Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialGrowthDegree.Dimension

section

/-! Leading coefficients from eventual inequalities of section dimensions. -/

open Filter _root_.Polynomial

theorem polynomial_leadingCoeff_nonneg_of_eventually_nat_eval_nonneg
    (P : Polynomial ℚ) (b : ℕ) (h : ∀ n : ℕ, b ≤ n → 0 ≤ P.eval (n : ℚ)) :
    0 ≤ P.leadingCoeff := by
  by_cases hd : P.degree ≤ 0
  · have he : P = Polynomial.C P.leadingCoeff := by
      simpa only [← Polynomial.coeff_natDegree,
        Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hd] using
        Polynomial.eq_C_of_degree_le_zero hd
    have hb := h b le_rfl
    rw [he, Polynomial.eval_C] at hb
    exact hb
  · by_contra hc
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos (lt_of_not_ge hd)
      (le_of_lt (lt_of_not_ge hc))).comp
      (tendsto_natCast_atTop_atTop (R := ℚ))
    obtain ⟨n, hn, hneg⟩ := ((eventually_ge_atTop b).and
      (ht.eventually_lt_atBot 0)).exists
    exact (h n hn).not_gt hneg

theorem polynomial_coeff_nonneg_of_eventually_nat_eval_nonneg
    (P : Polynomial ℚ) (d : ℕ) (hd : P.natDegree ≤ d)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → 0 ≤ P.eval (n : ℚ)) :
    0 ≤ P.coeff d := by
  rcases lt_or_eq_of_le hd with hd | hd
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hd]
  · rw [← hd, Polynomial.coeff_natDegree]
    exact polynomial_leadingCoeff_nonneg_of_eventually_nat_eval_nonneg P b h

theorem polynomial_coeff_le_of_eventually_nat_eval_le
    (P Q : Polynomial ℚ) (d : ℕ) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.coeff d ≤ Q.coeff d := by
  have hc := polynomial_coeff_nonneg_of_eventually_nat_eval_nonneg (Q - P) d
    (by simpa only [max_self] using Polynomial.natDegree_sub_le_of_le hQ hP) b
    (fun n hn => by simpa only [Polynomial.eval_sub, sub_nonneg] using h n hn)
  simpa only [Polynomial.coeff_sub, sub_nonneg] using hc

theorem polynomial_leadingCoeff_le_of_eventually_nat_eval_le
    (P Q : Polynomial ℚ) (hd : P.natDegree = Q.natDegree)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.leadingCoeff ≤ Q.leadingCoeff := by
  have hc := polynomial_coeff_le_of_eventually_nat_eval_le P Q P.natDegree
    le_rfl hd.symm.le b h
  rw [Polynomial.coeff_natDegree, hd, Polynomial.coeff_natDegree] at hc
  exact hc

theorem polynomial_leadingCoeff_comp_mul (P : Polynomial ℚ) (a : ℚ) (ha : a ≠ 0) :
    (P.comp (Polynomial.X * Polynomial.C a)).leadingCoeff =
      P.leadingCoeff * a ^ P.natDegree := by
  have hd : (Polynomial.X * Polynomial.C a).natDegree = 1 := by
    rw [Polynomial.natDegree_mul_C ha, Polynomial.natDegree_X]
  rw [Polynomial.leadingCoeff_comp (by omega :
    (Polynomial.X * Polynomial.C a).natDegree ≠ 0)]
  simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X,
    Polynomial.leadingCoeff_C, one_mul]

theorem polynomial_leadingCoeff_comp_add (P : Polynomial ℚ) (a : ℚ) :
    (P.comp (Polynomial.X + Polynomial.C a)).leadingCoeff = P.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by simp)]
  simp only [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

end

/-! Two-sided polynomial growth determines the degree of an eventual polynomial. -/

open _root_.Polynomial

theorem polynomial_natDegree_le_of_eventually_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff) (b : ℕ)
    (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hd
  have hlt : Q.natDegree < P.natDegree := Nat.lt_of_not_ge hd
  have hc := polynomial_coeff_le_of_eventually_nat_eval_le P Q P.natDegree le_rfl hlt.le b h
  rw [Polynomial.coeff_natDegree, Polynomial.coeff_eq_zero_of_natDegree_lt hlt] at hc
  exact hP.not_ge hc

theorem polynomial_natDegree_eq_of_power_growth
    (P : Polynomial ℚ) (hP : 0 < P.leadingCoeff)
    (g b c₁ c₂ D : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hlo : ∀ n : ℕ, b ≤ n → ((n : ℚ) + 1) ^ g ≤ P.eval ((n : ℚ) * c₁))
    (hhi : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ (D : ℚ) * ((n : ℚ) * c₂ + 1) ^ g) :
    P.natDegree = g := by
  have hc₁' : (c₁ : ℚ) ≠ 0 := by exact_mod_cast hc₁.ne'
  have hc₂' : (c₂ : ℚ) ≠ 0 := by exact_mod_cast hc₂.ne'
  let L : Polynomial ℚ := (Polynomial.X + Polynomial.C 1) ^ g
  let Q : Polynomial ℚ := P.comp (Polynomial.X * Polynomial.C (c₁ : ℚ))
  let T : Polynomial ℚ := Polynomial.X * Polynomial.C (c₂ : ℚ) + Polynomial.C 1
  let U : Polynomial ℚ := Polynomial.C (D : ℚ) * T ^ g
  have hLd : L.natDegree = g := by
    rw [Polynomial.natDegree_pow', Polynomial.natDegree_X_add_C, Nat.mul_one]
    simp only [Polynomial.leadingCoeff_X_add_C, one_pow, ne_eq, one_ne_zero, not_false_eq_true]
  have hLc : 0 < L.leadingCoeff := by
    rw [Polynomial.leadingCoeff_pow_X_add_C]
    exact zero_lt_one
  have hQd : Q.natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, Polynomial.natDegree_mul_C hc₁', Polynomial.natDegree_X, Nat.mul_one]
  have hTd : T.natDegree ≤ 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · rw [Polynomial.natDegree_mul_C hc₂', Polynomial.natDegree_X]
    · simp only [Polynomial.natDegree_C, zero_le]
  have hUd : U.natDegree ≤ g :=
    (Polynomial.natDegree_C_mul_le (D : ℚ) (T ^ g)).trans
      (by simpa only [Nat.mul_one] using Polynomial.natDegree_pow_le_of_le g hTd)
  have hlow := polynomial_natDegree_le_of_eventually_nat_eval_le L Q hLc b (fun n hn => by
    simpa only [L, Q, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_mul] using hlo n hn)
  have hhigh := polynomial_natDegree_le_of_eventually_nat_eval_le P U hP b (fun n hn => by
    simpa only [U, T, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_C] using hhi n hn)
  rw [hLd, hQd] at hlow
  exact le_antisymm (hhigh.trans hUd) hlow

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialGrowthDegree.Dimension
