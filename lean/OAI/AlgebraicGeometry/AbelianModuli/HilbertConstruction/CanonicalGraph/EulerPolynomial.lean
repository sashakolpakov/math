import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.LineBundleEulerPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness

/-! # Euler Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Polynomiality for the original canonical graph bundle, with the projective model and generated factors constructed from proved ampleness. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_eulerPolynomial_exists
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K))) :
    ∃ P : Polynomial ℚ, ∀ m : ℕ,
      P.eval (m : ℚ) = (CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
        (A.graphBundle.tensorPower m).sheaf : ℚ) := by
  obtain ⟨E⟩ := A.graphBundle_isAmple_overAlgClosed.exists_powerProjectiveEmbedding
    A.abelian.scheme.hom
  exact E.lineBundle_eulerPolynomial A.abelian.scheme.hom A.graphBundle

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
