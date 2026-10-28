import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.ReverseFiniteHomomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarized.NoetherianAffineProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.AffinePullback

/-! # Dual Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual dual of a polarized full-level abelian object over a Noetherian affine base admits an ample line bundle and a projective presentation. The bundle is pulled back along the constructed finite reverse homomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.dual_exists_ample_lineBundle_of_noetherian_affine (hδ : ∀ i, 0 < δ i) :
    ∃ L : Line.Bundles.LineBundle A.dual.abelian.scheme.left, L.IsAmple := by
  obtain ⟨m, _, hm, _, _⟩ := A.exists_finite_reverseHomomorphism hδ
  exact ⟨A.graphBundle.pullback m.left,
    A.graphBundle_isAmple_of_noetherian_affine.pullback_of_isAffineHom m.left⟩

def PolarizationData.PolarizedAbelianWithFullLevel.dualProjectivePresentation_of_noetherian_affine (hδ : ∀ i, 0 < δ i) :
    Projective.ProjectivePresentations.ProjectivePresentation A.dual.abelian.scheme :=
  (A.dual_exists_ample_lineBundle_of_noetherian_affine hδ).choose_spec.projectivePresentation
    A.dual.abelian.scheme.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
