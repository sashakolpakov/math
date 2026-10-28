import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwistedLine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerOrbitPolynomial

/-! # Line Bundle Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Projective line-bundle Euler polynomials compute all integer tensor
powers. A monomial formula for positive powers therefore determines inverse powers as well. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.lineBundleClass_integerEulerPolynomial
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X)
    (q : Line.Bundles.LineBundle.IsoClass X) :
    ∃ P : Polynomial ℚ, ∀ z : ℤ,
      P.eval (z : ℚ) = (LineBundle.EulerShifts.lineBundleClassEuler p (q * Line.Bundles.LineBundle.classOf M ^ z) : ℚ) := by
  obtain ⟨P, hP⟩ := E.lineBundleClass_eulerPolynomial p M q
  exact ⟨P, IntegerOrbitPolynomial.polynomial_orbit_all_integers (fun q => (LineBundle.EulerShifts.lineBundleClassEuler p q : ℚ))
    (Line.Bundles.LineBundle.classOf M) (fun q => E.lineBundleClass_eulerPolynomial p M q) q P hP⟩

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.integerEuler_of_monomial
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X)
    (d : ℕ) (c : ℤ)
    (hM : ∀ n : ℕ, 0 < n → CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (M.tensorPower n).sheaf = c * (n : ℤ) ^ d)
    (z : ℤ) : LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf M ^ z) = c * z ^ d := by
  obtain ⟨P, hP⟩ := E.lineBundleClass_integerEulerPolynomial p M 1
  let Q := Polynomial.monomial d (c : ℚ)
  have he : P = Q := by
    apply HilbertConstruction.Polynomial.EventualGrid.polynomial_eq_of_positive_nat_evals
    intro n hn
    have hp := hP (n : ℤ)
    simp only [Int.cast_natCast, zpow_natCast, one_mul,
      ← Line.Bundles.LineBundle.classOf_tensorPower, LineBundle.EulerShifts.lineBundleClassEuler_classOf] at hp
    rw [hp, hM n hn]
    simp only [Q, Polynomial.eval_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  have hz := hP z
  rw [he, Polynomial.eval_monomial, one_mul] at hz
  apply Int.cast_injective (α := ℚ)
  simpa only [Int.cast_mul, Int.cast_pow] using hz.symm

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.inverseEuler_of_monomial
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    {L : Line.Bundles.LineBundle X} (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L p) (M : Line.Bundles.LineBundle X)
    (d : ℕ) (c : ℤ)
    (hM : ∀ n : ℕ, 0 < n → CohomologyEulerCharacteristic.coefficientEulerCharacteristic p (M.tensorPower n).sheaf = c * (n : ℤ) ^ d) :
    LineBundle.EulerShifts.lineBundleClassEuler p (Line.Bundles.LineBundle.classOf M)⁻¹ = (-1 : ℤ) ^ d * c := by
  simpa only [zpow_neg_one, mul_comm] using E.integerEuler_of_monomial p M d c hM (-1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
