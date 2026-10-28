import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldEulerFormula

/-! # Integer Euler -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The Euler monomial of the canonical graph bundle computes its integer
powers, including its inverse, over every field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_integerPower_euler
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) (z : ℤ) :
    LineBundle.EulerShifts.lineBundleClassEuler A.abelian.scheme.hom (Line.Bundles.LineBundle.classOf A.graphBundle ^ z) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf * z ^ g := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overField.exists_powerProjectiveEmbedding
    A.abelian.scheme.hom
  exact E.integerEuler_of_monomial A.abelian.scheme.hom A.graphBundle g
    (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf)
    (A.graphBundle_positivePower_euler_overField hN hNk) z

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_inverse_euler
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    LineBundle.EulerShifts.lineBundleClassEuler A.abelian.scheme.hom (Line.Bundles.LineBundle.classOf A.graphBundle)⁻¹ =
      (-1 : ℤ) ^ g * CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom A.graphBundle.sheaf := by
  simpa only [zpow_neg_one, mul_comm] using A.graphBundle_integerPower_euler hN hNk (-1)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
