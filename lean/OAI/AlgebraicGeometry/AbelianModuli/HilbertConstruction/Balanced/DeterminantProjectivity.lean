import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.VeroneseProjectivePresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Veronese.ProjectiveBaseCompatibility

/-! # Determinant Projectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantProjectivity

noncomputable section

/-! The actual balanced determinant projective spectrum has a
projective presentation over its coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

def transportProjectivePresentation {S : Scheme.{u}} {X Y : Over S}
    (e : X ≅ Y) (P : Projective.ProjectivePresentations.ProjectivePresentation Y) : Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := by
    change IsClosedImmersion (e.hom.left ≫ P.embedding.left)
    let : IsIso e.hom.left := (Over.forget S).map_isIso e.hom
    let : IsClosedImmersion P.embedding.left := P.closedImmersion
    infer_instance

theorem balancedDeterminant_projective_presentation
    (R : Type u) [CommRing R] {r m : ℕ} (hr : 0 < r) (i : Fin m) :
    Nonempty (Projective.ProjectivePresentations.ProjectivePresentation (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (DeterminantGrading.balancedDeterminantGrading R r m i)))) := by
  obtain ⟨N, ⟨P⟩⟩ := VeroneseProjectivePresentation.balancedDeterminant_veronese_projective_presentation R hr i
  exact ⟨transportProjectivePresentation
    (Veronese.ProjectiveBaseCompatibility.veroneseProjectiveOverIso (DeterminantGrading.balancedDeterminantGrading R r m i) (N : ℕ)) P⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.DeterminantProjectivity
