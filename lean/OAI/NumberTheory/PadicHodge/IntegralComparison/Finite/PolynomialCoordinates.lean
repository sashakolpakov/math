import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators

/-! # Polynomial Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialCoordinates

noncomputable section

/-! Finite coefficient coordinates and their convolution, with bounds
large enough to contain the actual polynomial support. -/

open _root_.Polynomial

variable {R : Type*} [CommSemiring R]

theorem expansion (P : Polynomial R) (n : ℕ) (hn : P.natDegree ≤ n) :
    P = ∑ i : Fin (n + 1), monomial i (P.coeff i) := by
  classical
  calc
    P = ofFn (n + 1) (fun i => P.coeff i) :=
      (ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le hn)).symm
    _ = _ := ofFn_eq_sum_monomial _

theorem coeff_expansion (P : Polynomial R) (n : ℕ) (hn : P.natDegree ≤ n) (k : ℕ) :
    P.coeff k = ∑ i : Fin (n + 1), if (i : ℕ) = k then P.coeff i else 0 := by
  have h := congrArg (fun p : Polynomial R => p.coeff k) (expansion P n hn)
  simpa only [finsetSum_coeff, coeff_monomial] using h

theorem product_expansion (P Q : Polynomial R) (n m : ℕ)
    (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) :
    P * Q = ∑ t : Fin (n + 1) × Fin (m + 1),
      monomial (t.1.val + t.2.val) (P.coeff t.1 * Q.coeff t.2) := by
  conv_lhs => rw [expansion P n hn, expansion Q m hm]
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact monomial_mul_monomial _ _ _ _

theorem coeff_product_expansion (P Q : Polynomial R) (n m : ℕ)
    (hn : P.natDegree ≤ n) (hm : Q.natDegree ≤ m) (k : ℕ) :
    (P * Q).coeff k = ∑ t : Fin (n + 1) × Fin (m + 1),
      if t.1.val + t.2.val = k then P.coeff t.1 * Q.coeff t.2 else 0 := by
  have h := congrArg (fun p : Polynomial R => p.coeff k) (product_expansion P Q n m hn hm)
  simpa only [finsetSum_coeff, coeff_monomial] using h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.PolynomialCoordinates
