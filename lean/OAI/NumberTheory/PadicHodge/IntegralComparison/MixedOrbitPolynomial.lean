import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitNewton
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Mixed Orbit Polynomial -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitPolynomial

noncomputable section

/-! Polynomial reconstruction of the three tensor exponents `n²m`, `nm`,
and `m`. Ordered mixed differences of total order greater than `d` vanish;
the resulting polynomial in `m` has degree at most `d`, and its coefficient
of `m^d` is a polynomial in `n` of degree at most `2d`. -/

open _root_.Polynomial

def scaledChoose (a : ℚ) (i : ℕ) : Polynomial ℚ :=
  C (1 / (i.factorial : ℚ)) * (descPochhammer ℚ i).comp (C a * X)

theorem scaledChoose_eval (a m i : ℕ) :
    (scaledChoose (a : ℚ) i).eval (m : ℚ) = ((a * m).choose i : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp only [scaledChoose, eval_mul, eval_C, eval_comp, eval_X, Nat.cast_mul]
  ring

theorem scaledChoose_natDegree (a : ℚ) (i : ℕ) :
    (scaledChoose a i).natDegree ≤ i := by
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  rw [descPochhammer_natDegree]
  calc
    i * (C a * X : Polynomial ℚ).natDegree ≤ i * 1 :=
      Nat.mul_le_mul_left i ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X]))
    _ = i := Nat.mul_one i

theorem scaledChoose_coeff (a : ℚ) (i : ℕ) :
    (scaledChoose a i).coeff i = a ^ i / (i.factorial : ℚ) := by
  have hi : (descPochhammer ℚ i).coeff i = 1 := by
    simpa only [← coeff_natDegree, descPochhammer_natDegree] using
      (monic_descPochhammer (R := ℚ) i).leadingCoeff
  simp only [scaledChoose, coeff_C_mul, comp_C_mul_X_coeff, hi, one_mul]
  ring

def term (c : ℕ → ℕ → ℕ → ℚ) (n i j k : ℕ) : Polynomial ℚ :=
  C (c i j k) * (scaledChoose ((n * n : ℕ) : ℚ) i * scaledChoose (n : ℚ) j * scaledChoose 1 k)

theorem term_natDegree (c : ℕ → ℕ → ℕ → ℚ) (n i j k : ℕ) :
    (term c n i j k).natDegree ≤ i + j + k := by
  apply (natDegree_C_mul_le _ _).trans
  exact natDegree_mul_le.trans (Nat.add_le_add
    (natDegree_mul_le.trans (Nat.add_le_add (scaledChoose_natDegree _ _) (scaledChoose_natDegree _ _)))
    (scaledChoose_natDegree _ _))

theorem term_coeff_top (c : ℕ → ℕ → ℕ → ℚ) (n i j k : ℕ) :
    (term c n i j k).coeff (i + j + k) =
      (c i j k / ((i.factorial : ℚ) * (j.factorial : ℚ) * (k.factorial : ℚ))) *
        (n : ℚ) ^ (2 * i + j) := by
  rw [term, coeff_C_mul,
    coeff_mul_add_eq_of_natDegree_le
      (natDegree_mul_le.trans (Nat.add_le_add (scaledChoose_natDegree _ _) (scaledChoose_natDegree _ _)))
      (scaledChoose_natDegree _ _),
    coeff_mul_add_eq_of_natDegree_le (scaledChoose_natDegree _ _) (scaledChoose_natDegree _ _),
    scaledChoose_coeff, scaledChoose_coeff, scaledChoose_coeff]
  simp only [one_pow, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev, pow_add, pow_mul, pow_two, mul_pow]
  ring

def polynomial (c : ℕ → ℕ → ℕ → ℚ) (d n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
    ∑ k ∈ Finset.range (d + 1), term c n i j k

def topPolynomial (c : ℕ → ℕ → ℕ → ℚ) (d : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
    ∑ k ∈ Finset.range (d + 1),
      if i + j + k = d then
        C (c i j k / ((i.factorial : ℚ) * (j.factorial : ℚ) * (k.factorial : ℚ))) * X ^ (2 * i + j)
      else 0

theorem polynomial_natDegree (c : ℕ → ℕ → ℕ → ℚ) (d n : ℕ)
    (hc : ∀ i j k : ℕ, d < i + j + k → c i j k = 0) :
    (polynomial c d n).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_sum_le_of_forall_le
  intro k _
  by_cases h : i + j + k ≤ d
  · exact (term_natDegree c n i j k).trans h
  · simp only [term, hc i j k (Nat.lt_of_not_ge h), map_zero, zero_mul, natDegree_zero, Nat.zero_le]

theorem topPolynomial_natDegree (c : ℕ → ℕ → ℕ → ℚ) (d : ℕ) :
    (topPolynomial c d).natDegree ≤ 2 * d := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_sum_le_of_forall_le
  intro k _
  split_ifs with h
  · apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_X_pow]
    omega
  · simp only [natDegree_zero, Nat.zero_le]

theorem topPolynomial_coeff (c : ℕ → ℕ → ℕ → ℚ) (d : ℕ) :
    (topPolynomial c d).coeff (2 * d) = c d 0 0 / (d.factorial : ℚ) := by
  simp only [topPolynomial, finsetSum_coeff]
  rw [Finset.sum_eq_single_of_mem d (Finset.mem_range.mpr (Nat.lt_succ_self d)) (by
    intro i _ hid
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hs : i + j + k = d
    · have hp : 2 * i + j ≠ 2 * d := by omega
      simp only [ite_eq_left hs, coeff_C_mul, coeff_X_pow, ite_eq_right hp.symm, mul_zero]
    · rw [ite_eq_right hs, coeff_zero])]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ d)) (by
    intro j _ hj
    apply Finset.sum_eq_zero
    intro k _
    have hs : d + j + k ≠ d := by omega
    rw [ite_eq_right hs, coeff_zero])]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ d)) (by
    intro k _ hk
    have hs : d + 0 + k ≠ d := by omega
    rw [ite_eq_right hs, coeff_zero])]
  simp

theorem coefficient_topPolynomial (c : ℕ → ℕ → ℕ → ℚ) (d n : ℕ)
    (hc : ∀ i j k : ℕ, d < i + j + k → c i j k = 0) :
    (polynomial c d n).coeff d = (topPolynomial c d).eval (n : ℚ) := by
  simp only [polynomial, topPolynomial, finsetSum_coeff, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases he : i + j + k = d
  · rw [ite_eq_left he, eval_mul, eval_C, eval_pow, eval_X, ← he, term_coeff_top]
  · rw [ite_eq_right he, eval_zero]
    by_cases hlt : i + j + k < d
    · exact coeff_eq_zero_of_natDegree_lt ((term_natDegree c n i j k).trans_lt hlt)
    · simp only [term, hc i j k (by omega), map_zero, zero_mul, coeff_zero]

theorem polynomial_eval (c : ℕ → ℕ → ℕ → ℚ) (d n m : ℕ) :
    (polynomial c d n).eval (m : ℚ) =
      ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1),
        ∑ k ∈ Finset.range (d + 1),
          ((n * n * m).choose i : ℚ) * ((n * m).choose j : ℚ) * (m.choose k : ℚ) * c i j k := by
  simp only [polynomial, term, eval_finsetSum, eval_mul, eval_C]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [scaledChoose_eval, scaledChoose_eval]
  have h := scaledChoose_eval 1 m k
  simp only [Nat.cast_one, one_mul] at h
  rw [h]
  ring

theorem orbit_polynomials_with_top {G : Type*} [AddCommGroup G]
    (T U V : AddMonoid.End G) (φ : G →+ ℚ) (x : G) (d : ℕ)
    (hzero : ∀ i j k : ℕ, d < i + j + k →
      ((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x)) = 0) :
    ∃ (P : ℕ → Polynomial ℚ) (D : Polynomial ℚ),
      D.natDegree ≤ 2 * d ∧
      (∀ n : ℕ, (P n).natDegree ≤ d) ∧
      (∀ n m : ℕ, (P n).eval (m : ℚ) = φ ((T ^ (n * n * m)) ((U ^ (n * m)) ((V ^ m) x)))) ∧
      (∀ n : ℕ, (P n).coeff d = D.eval (n : ℚ)) ∧
      D.coeff (2 * d) = φ (((T - 1) ^ d) x) / (d.factorial : ℚ) := by
  let c := MixedOrbitNewton.coefficient T U V φ x
  have hc (i j k : ℕ) (h : d < i + j + k) : c i j k = 0 := by
    change φ (((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x))) = 0
    rw [hzero i j k h, map_zero]
  refine ⟨polynomial c d, topPolynomial c d, topPolynomial_natDegree c d,
    fun n => polynomial_natDegree c d n hc, ?_,
    fun n => coefficient_topPolynomial c d n hc, ?_⟩
  · intro n m
    rw [polynomial_eval]
    exact (MixedOrbitNewton.triple_newton T U V φ x d hzero (n * n * m) (n * m) m).symm
  · rw [topPolynomial_coeff]
    rfl

theorem orbit_polynomials {G : Type*} [AddCommGroup G]
    (T U V : AddMonoid.End G) (φ : G →+ ℚ) (x : G) (d : ℕ)
    (hzero : ∀ i j k : ℕ, d < i + j + k →
      ((T - 1) ^ i) (((U - 1) ^ j) (((V - 1) ^ k) x)) = 0) :
    ∃ (P : ℕ → Polynomial ℚ) (D : Polynomial ℚ),
      D.natDegree ≤ 2 * d ∧
      (∀ n : ℕ, (P n).natDegree ≤ d) ∧
      (∀ n m : ℕ, (P n).eval (m : ℚ) = φ ((T ^ (n * n * m)) ((U ^ (n * m)) ((V ^ m) x)))) ∧
      (∀ n : ℕ, (P n).coeff d = D.eval (n : ℚ)) := by
  obtain ⟨P, D, hD, hP, hv, ht, _⟩ := orbit_polynomials_with_top T U V φ x d hzero
  exact ⟨P, D, hD, hP, hv, ht⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedOrbitPolynomial
