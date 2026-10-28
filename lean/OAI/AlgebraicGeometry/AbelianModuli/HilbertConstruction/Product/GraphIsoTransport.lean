import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphIsomorphismTransport

/-! # Graph Iso Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.GraphIsoTransport

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
universe u
variable {S : Scheme.{u}} {X X' Y Y' : Over S}
variable [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
variable [Flat X'.hom] [LocallyOfFinitePresentation X'.hom] [IsSeparated Y'.hom]
variable (e : X ≅ X') (d : Y ≅ Y') {n : ℕ}
variable (j' : X' ⊗ Y' ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) [IsClosedImmersion j'.left]
omit [Flat X.hom] [LocallyOfFinitePresentation X.hom] [IsSeparated Y.hom]
  [Flat X'.hom] [LocallyOfFinitePresentation X'.hom] [IsSeparated Y'.hom] in
private theorem productIsoComposite_closed :
    IsClosedImmersion ((tensorIso e d).hom ≫ j').left :=
  @IsClosedImmersion.comp _ _ _ _ _ (Grassmann.ProjectivePresentation.overIso_closedImmersion (tensorIso e d)) inferInstance

theorem productGraphIsoTransport (R : Polynomial ℚ) (p : X ⟶ Y) :
    letI := productIsoComposite_closed e d j'
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial ((tensorIso e d).hom ≫ j') R p ↔
      Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial j' R (CategoryTheory.Isomorphisms.IsoConjugateMap.isoConjugateMap e d p) := by
  let := productIsoComposite_closed e d j'
  exact Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial.transport_iff e d p
    ((tensorIso e d).hom ≫ j') j' rfl R

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.GraphIsoTransport
