import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.ReembeddingComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Family Conjugation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyConjugation

noncomputable section

/-! Conjugating a family morphism by source and target isomorphisms transports its actual ideal-defined graph through the corresponding product isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

variable {S : Scheme.{u}} {A A' B B' : Over S} (eA : A' ≅ A) (eB : B' ≅ B)

def conjugateFamilyMorphism (p : A ⟶ B) : A' ⟶ B' := eA.hom ≫ p ≫ eB.inv

theorem conjugateFamilyMorphism_graph (p : A ⟶ B) :
    MorphismGraphFamilies.familyGraph (conjugateFamilyMorphism eA eB p) ≫ (eA.hom ⊗ₘ eB.hom) = eA.hom ≫ MorphismGraphFamilies.familyGraph p := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [MorphismGraphFamilies.familyGraph]
  · simp [MorphismGraphFamilies.familyGraph, conjugateFamilyMorphism, Category.assoc]

local instance graphConjugationTensorClosed : IsClosedImmersion (eA.hom ⊗ₘ eB.hom).left :=
  Grassmann.ProjectivePresentation.overIso_closedImmersion (tensorIso eA eB)

local instance graphConjugationCompositeClosed {P : Over S} (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left] :
    IsClosedImmersion ((eA.hom ⊗ₘ eB.hom) ≫ j).left :=
  inferInstanceAs (IsClosedImmersion ((eA.hom ⊗ₘ eB.hom).left ≫ j.left))

theorem morphismGraphFamily_conjugation_reembed
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    [Flat A'.hom] [LocallyOfFinitePresentation A'.hom] [IsSeparated B'.hom] (p : A ⟶ B) :
    (MorphismGraphFamilies.morphismGraphFamily (conjugateFamilyMorphism eA eB p)).reembed (eA.hom ⊗ₘ eB.hom) =
      MorphismGraphFamilies.morphismGraphFamily p := by
  change (Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph (conjugateFamilyMorphism eA eB p))).reembed
    (eA.hom ⊗ₘ eB.hom) = _
  rw [Closed.Families.FlatClosedFamily.ofEmbedding_reembed]
  have : IsClosedImmersion (MorphismGraphFamilies.familyGraph (conjugateFamilyMorphism eA eB p) ≫ (eA.hom ⊗ₘ eB.hom)).left :=
    inferInstanceAs (IsClosedImmersion
      ((MorphismGraphFamilies.familyGraph (conjugateFamilyMorphism eA eB p)).left ≫ (eA.hom ⊗ₘ eB.hom).left))
  apply Closed.Families.FlatClosedFamily.ofEmbedding_eq_of_iso _ (MorphismGraphFamilies.morphismGraphFamily p) (eA ≪≫ MorphismGraphFamilies.morphismGraphFamilyIso p)
  change eA.hom ≫ (Closed.Families.FlatClosedFamily.ofEmbeddingIso (MorphismGraphFamilies.familyGraph p)).hom ≫
    (Closed.Families.FlatClosedFamily.ofEmbedding (MorphismGraphFamilies.familyGraph p)).inclusion = _
  rw [Closed.Families.FlatClosedFamily.ofEmbeddingIso_inclusion]
  exact (conjugateFamilyMorphism_graph eA eB p).symm

theorem morphismGraphFamily_conjugation_reembedding
    [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
    [Flat A'.hom] [LocallyOfFinitePresentation A'.hom] [IsSeparated B'.hom]
    (p : A ⟶ B) {P : Over S} (j : A ⊗ B ⟶ P) [IsClosedImmersion j.left] :
    (MorphismGraphFamilies.morphismGraphFamily (conjugateFamilyMorphism eA eB p)).reembed ((eA.hom ⊗ₘ eB.hom) ≫ j) =
      (MorphismGraphFamilies.morphismGraphFamily p).reembed j :=
  ((MorphismGraphFamilies.morphismGraphFamily (conjugateFamilyMorphism eA eB p)).reembed_comp (eA.hom ⊗ₘ eB.hom) j).symm.trans
    (congrArg (fun F : Closed.Families.FlatClosedFamily (A ⊗ B) => F.reembed j)
      (morphismGraphFamily_conjugation_reembed eA eB p))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyConjugation
