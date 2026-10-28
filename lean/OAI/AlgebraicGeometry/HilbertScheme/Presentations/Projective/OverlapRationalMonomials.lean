import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapFunctionField
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapExponents
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalTransitionExponentComparison
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RationalPowerDenominators

/-! # Overlap Rational Monomials -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRationalMonomials

noncomputable section

/-! Every actual invertible overlap section maps to a rational
coordinate monomial whose exponent is its canonical overlap exponent. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1)) (hji : j ≠ i)

theorem projectiveOverlapFunctionFieldMap_of_equation
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j))
    (c : Kˣ) (a b : ℕ)
    (h : z * OverlapSectionUnits.projectiveOverlapRatio K i j ^ b =
      OverlapSectionUnits.projectiveOverlapConstant K i j (c : K) * OverlapSectionUnits.projectiveOverlapRatio K i j ^ a) :
    OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j z = RationalTransitionExponentComparison.rationalProjectiveMonomial c i j ((a : ℤ) - b) := by
  have he := congrArg (OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j) h
  rw [map_mul, map_pow, map_mul, map_pow, OverlapFunctionField.projectiveOverlapFunctionFieldMap_ratio,
    OverlapFunctionField.projectiveOverlapFunctionFieldMap_constant] at he
  exact RationalPowerDenominators.rational_power_of_cleared_denominator _ _ _ (RationalCoordinateDegrees.rationalProjectiveCoordinate_ne_zero i j) a b he

theorem projectiveOverlapFunctionFieldMap_unit
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ) :
    ∃ c : Kˣ, OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n),
      OverlapSectionUnits.projectiveDoubleOpen K i j)) =
        RationalTransitionExponentComparison.rationalProjectiveMonomial c i j (OverlapExponents.projectiveOverlapUnitExponent K i j hji z) := by
  obtain ⟨c, a, b, h⟩ := OverlapSectionUnits.projectiveOverlap_unit_powers K i j hji z
  have he := projectiveOverlapFunctionFieldMap_of_equation K i j (z : _) c a b h
  rw [← OverlapExponents.projectiveOverlapUnitExponent_of_equation K i j hji z c a b h] at he
  exact ⟨c, he⟩

theorem projectiveOverlap_exponents_of_functionField_cocycle
    (k : Fin (n + 1)) (hkj : k ≠ j) (hki : k ≠ i)
    (x : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i j)ˣ)
    (y : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K j k)ˣ)
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), OverlapSectionUnits.projectiveDoubleOpen K i k)ˣ)
    (h : OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j (x : _) * OverlapFunctionField.projectiveOverlapFunctionFieldMap K j k (y : _) =
      OverlapFunctionField.projectiveOverlapFunctionFieldMap K i k (z : _)) :
    OverlapExponents.projectiveOverlapUnitExponent K i j hji x = OverlapExponents.projectiveOverlapUnitExponent K j k hkj y ∧
      OverlapExponents.projectiveOverlapUnitExponent K j k hkj y = OverlapExponents.projectiveOverlapUnitExponent K i k hki z := by
  obtain ⟨c, hc⟩ := projectiveOverlapFunctionFieldMap_unit K i j hji x
  obtain ⟨d, hd⟩ := projectiveOverlapFunctionFieldMap_unit K j k hkj y
  obtain ⟨e, he⟩ := projectiveOverlapFunctionFieldMap_unit K i k hki z
  rw [hc, hd, he] at h
  exact RationalTransitionExponentComparison.rational_transition_exponents_agree i j k hji.symm hkj.symm hki.symm c d e _ _ _ h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapRationalMonomials
