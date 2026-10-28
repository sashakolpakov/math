import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.CohomologyTerminal

/-! # Free Sheaf Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FreeSheafSections.Construction

noncomputable section

/-! The free abelian sheaf on a representable corepresents sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{v}] (U : C)

abbrev freeAbelianRepresentableSheaf : CategoryTheory.Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

def freeAbelianSheafHomSectionsEquiv (F : CategoryTheory.Sheaf J AddCommGrpCat.{v}) :
    (freeAbelianRepresentableSheaf J U ⟶ F) ≃ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).trans
    (((Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv _ _).trans yonedaEquiv)

theorem freeAbelianSheafHomSectionsEquiv_naturality
    {F G : CategoryTheory.Sheaf J AddCommGrpCat.{v}} (φ : F ⟶ G)
    (q : freeAbelianRepresentableSheaf J U ⟶ F) :
    freeAbelianSheafHomSectionsEquiv J U G (q ≫ φ) =
      φ.hom.app (op U) (freeAbelianSheafHomSectionsEquiv J U F q) := by
  dsimp only [freeAbelianSheafHomSectionsEquiv, Equiv.trans_apply]
  rw [(sheafificationAdjunction J AddCommGrpCat).homEquiv_naturality_right q φ]
  rw [(Adjunction.whiskerRight Cᵒᵖ AddCommGrpCat.adj).homEquiv_naturality_right]
  exact yonedaEquiv_comp _ _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FreeSheafSections.Construction
