import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorRefinementCoordinates

/-! # Functor Object Reassociation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorObjectReassociation.SectionFunctorObjectReassociation

noncomputable section

/-! Reassociate precomposition at the level of section complexes,
before applying a Cech total or a homology functor. -/
open _root_.CategoryTheory
universe a b c d e f g h v w
variable {A : Type a} [Category.{b} A] [Preadditive A]
  {B : Type c} [Category.{d} B] [Abelian B]
  {C : Type e} [Category.{f} C] {D : Type g} [Category.{h} D]
  {E : Type v} [Category.{w} E]
  (S : A ⥤ (Eᵒᵖ ⥤ B)) [S.Additive] (K : CochainComplex A ℕ)
  (G : C ⥤ D) (F : D ⥤ E)

theorem equality :
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback G).mapHomologicalComplex (.up ℕ)).obj
      (FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.oldSections S K F) =
    FunctorRefinementCoordinates.SectionFunctorRefinementCoordinates.newSections S K G F := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.FunctorObjectReassociation.SectionFunctorObjectReassociation
