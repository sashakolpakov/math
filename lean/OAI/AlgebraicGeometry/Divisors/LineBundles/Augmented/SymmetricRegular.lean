import OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricPolynomial
import Mathlib.Algebra.Polynomial.Coeff

/-! # Symmetric Regular -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricRegular.BundleCycles

noncomputable section

/-! The distinguished coordinate is regular in the actual augmented
symmetric algebra, over any coefficient ring and module. -/

variable (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]

theorem augmentedSymmetricVariable_isRegular : IsRegular (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) := by
  have hleft : IsLeftRegular (SymmetricChart.BundleCycles.augmentedSymmetricVariable R M) := by
    intro a b h
    apply (SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialEquiv R M).injective
    have he := congrArg (SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap R M) h
    rw [map_mul, map_mul, SymmetricPolynomial.BundleCycles.augmentedSymmetricPolynomialMap_variable] at he
    exact Polynomial.isRegular_X.left he
  exact ⟨hleft, fun a b h => hleft ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Augmented.SymmetricRegular.BundleCycles
