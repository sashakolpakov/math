import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.CrystallinePlusShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.IntegerPolynomialNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrimeToEvaluation
import OAI.NumberTheory.PadicHodge.IntegralComparison.EvenCharacteristicEvaluation
import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveBettiDimension

/-! # Crystalline Polynomial Criterion -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! Exact determinants of the genuine prime-to-characteristic
Frobenius shifts determine the full original crystalline characteristic
polynomial. The rank and the sign are supplied by the proved projective
comparison for the given model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CrystallineFunctoriality.CM

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq)
  (j : K →+* ℂ)
  (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)

include j P

theorem GeometricComparison.Geometry.AbelianH1Model.native_crystalline_finrank_even : Even (Module.finrank ℚ_[q] A.Crystalline) := by
  rw [CrystallineDimension.FrobeniusSlope.crystalline_finrank_eq_betti A j P,
    A.projective_complexBetti_finrank j P]
  exact even_two_mul _

theorem GeometricComparison.Geometry.AbelianH1Model.native_crystalline_charpoly_of_plus_pullback_determinants (b : ℕ)
    (hdet : ∀ n : ℕ, b ≤ n → ¬q ∣ n →
      (GeometricComparison.Crystalline.CoefficientAdapter.rationalPullback q
        (((n : AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.AlgebraicEnd A.specialFiber.scheme) +
          AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.algebraicFrobenius (ZMod q) A.specialFiber.scheme).toMul.hom.hom)).det =
        ((A.nativeIntegerFrobeniusPolynomial.eval (-(n : ℤ)) : ℤ) : ℚ_[q])) :
    letI : FiniteDimensional ℚ_[q] A.Crystalline :=
      CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
    A.crystallineFrobenius.charpoly =
      A.nativeIntegerFrobeniusPolynomial.map (Int.castRingHom ℚ_[q]) := by
  let : FiniteDimensional ℚ_[q] A.Crystalline :=
    CrystallineDimension.FrobeniusSlope.crystalline_finite A j P
  apply IntegralComparison.PrimeToEvaluation.Negative.eq_integer_polynomial _ _ q b (Fact.out : q.Prime).one_lt
  intro n hn hqn
  rw [IntegralComparison.EvenCharacteristicEvaluation.eval_neg _ _ (A.native_crystalline_finrank_even j P),
    ← A.crystallinePullback_plus_nat j P n]
  exact hdet n hn hqn

end

end OAI.NumberTheory.PadicHodge
