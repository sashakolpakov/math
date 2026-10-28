import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ProjectivePresentation

noncomputable section

/-! Convert an actual closed embedding into affine-base projective
space to HilbertConstruction's relative projective presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def affine_projective_relative_presentation {R : Type} [CommRing R]
    {X : Over (Spec (.of R))} (n : ℕ) (i : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace R n)
    [IsClosedImmersion i.left] : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation X := by
  let e := AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n
  have : IsIso e.inv.left := ((Over.forget (Spec (.of R))).mapIso e).isIso_inv
  exact ⟨n, i ≫ e.inv, inferInstanceAs (IsClosedImmersion (i.left ≫ e.inv.left))⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.ProjectivePresentation
