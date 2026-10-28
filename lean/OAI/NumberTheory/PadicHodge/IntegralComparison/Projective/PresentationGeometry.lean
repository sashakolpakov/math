import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projectivity

/-! # Presentation Geometry -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PresentationGeometry

noncomputable section

/-! An actual relative projective presentation gives the native
finite-dimensional projective embedding predicate. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
universe u
variable (R : Type u) [CommRing R] (X : Over (Spec (.of R)))

def embedding (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    X ⟶ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R P.dimension :=
  P.embedding ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension).hom

instance embedding_closed (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    IsClosedImmersion (PresentationGeometry.embedding R X P).left := by
  let e := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) P.dimension
  let : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  exact inferInstanceAs (IsClosedImmersion (P.embedding.left ≫ e.hom.left))

theorem projectiveOver (P : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X) :
    Projectivity.Construction.ProjectiveOver R X.hom :=
  ⟨P.dimension, (PresentationGeometry.embedding R X P).left, embedding_closed R X P, (PresentationGeometry.embedding R X P).w⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PresentationGeometry
