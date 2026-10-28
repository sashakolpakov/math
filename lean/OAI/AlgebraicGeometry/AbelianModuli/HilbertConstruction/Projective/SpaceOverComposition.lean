import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Space Over Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceOverComposition

noncomputable section

/-! The projective space over an intermediate base, viewed over the original base, is the product of the original projective space with the intermediate base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def overMapPullbackProductIso {S : Scheme.{u}} (M A : Over S) :
    (Over.map M.hom).obj ((Over.pullback M.hom).obj A) ≅ A ⊗ M :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans pullback.condition)

def projectiveSpaceOverCompositionIso {S : Scheme.{u}} (M : Over S) (n : ℕ) :
    (Over.map M.hom).obj (ProjectivePresentations.projectiveSpaceOver M.left n) ≅ ProjectivePresentations.projectiveSpaceOver S n ⊗ M :=
  (Over.map M.hom).mapIso (SpaceBaseChange.projectiveSpaceOverBaseChangeIso M.hom n) ≪≫
    overMapPullbackProductIso M (ProjectivePresentations.projectiveSpaceOver S n)

def projectiveSpaceIdentityPresentation (S : Scheme.{u}) (n : ℕ) :
    ProjectivePresentations.ProjectivePresentation (ProjectivePresentations.projectiveSpaceOver S n) where
  dimension := n
  embedding := 𝟙 _
  closedImmersion := inferInstanceAs (IsClosedImmersion (𝟙 (ProjectivePresentations.projectiveSpaceOver S n).left))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceOverComposition
