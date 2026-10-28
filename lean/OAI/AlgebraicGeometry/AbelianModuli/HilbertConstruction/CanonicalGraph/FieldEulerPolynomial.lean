import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.FieldProjectivity

/-! # Field Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The polynomial for the original graph-bundle Euler sequence exists over every field, using the proved descent of graph ampleness. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_eulerPolynomial_exists_overField
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) :
    ∃ P : Polynomial ℚ, ∀ m : ℕ,
      P.eval (m : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
        (A.graphBundle.tensorPower m).sheaf : ℚ) := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overField.exists_powerProjectiveEmbedding
    A.abelian.scheme.hom
  exact E.lineBundle_eulerPolynomial A.abelian.scheme.hom A.graphBundle

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
