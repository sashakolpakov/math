import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientDynamics
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearch
import OAI.Algorithms.SubexponentialSAT.Subexp.ElementaryMatrix

namespace OAI.Algorithms

/-!
# Identifying normalized interpolation coefficients

The physical checker tests normalized coefficients by repeated weighted
Pascal shifts. Multiplication by `2^j` gives the unique binomial interpolant
already used by the layout. This proof identifies coefficient values, without
requiring two search procedures to inspect candidates in the same order.
-/

namespace SubexponentialSAT.Subexp.CoefficientNormalization

open scoped BigOperators

def unnormalize {K : Type*} [CommRing K] (xs : List K) (j : ℕ) : K :=
  xs.getD j 0 * 2 ^ j

/-- Any successful normalized checker output gives the same unnormalized
coefficient function, including the zero extension above its length. -/
theorem coefficients_eq (p A R : ℕ) (hp : 0 < p) (xs : List (ZMod p))
    (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val)) :
    unnormalize xs = CoefficientSearch.coefficientsNat p A R := by
  have hfinite : (fun j : Fin R => unnormalize xs j.val) =
      CoefficientSearch.coefficients p A R := by
    apply (BinomialInterpolation.existsUnique_binomial_interpolation
      (K := ZMod p) A R (fun d => (-1 : ZMod p) ^ (A + d.val))).unique
    · intro d
      have h := hcheck d
      unfold CoefficientDynamics.evaluate at h
      rw [hlength, ← Fin.sum_univ_eq_sum_range] at h
      exact h
    · exact CoefficientSearch.coefficients_spec p A R hp
  funext j
  by_cases hj : j < R
  · have h := congrFun hfinite ⟨j, hj⟩
    simpa only [CoefficientSearch.coefficientsNat, dite_eq_left hj] using h
  · rw [unnormalize, List.getD_eq_default xs 0 (by omega), zero_mul,
      CoefficientSearch.coefficientsNat_eq_zero p A R j (by omega)]

theorem coefficient_eq (p A R : ℕ) (hp : 0 < p) (xs : List (ZMod p))
    (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val))
    (j : ℕ) :
    xs.getD j 0 * (2 : ZMod p) ^ j = CoefficientSearch.coefficientsNat p A R j :=
  congrFun (coefficients_eq p A R hp xs hlength hcheck) j

/-- The actual matrix generated from the normalized list is the layout's
matrix, by coefficient uniqueness. -/
theorem jointMatrix_eq {p r Q Δ : ℕ} [Fact p.Prime]
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) (xs : List (ZMod p))
    (hlength : xs.length = R)
    (hcheck : ∀ d : Fin R,
      CoefficientDynamics.evaluate xs (A + d.val) = (-1 : ZMod p) ^ (A + d.val)) :
    ElementaryMatrix.jointMatrixDP i t g xs.length (unnormalize xs) =
      ElementaryMatrix.jointMatrixDP i t g R (CoefficientSearch.coefficientsNat p A R) := by
  rw [hlength, coefficients_eq p A R (Fact.out : p.Prime).pos xs hlength hcheck]

end SubexponentialSAT.Subexp.CoefficientNormalization

end OAI.Algorithms
