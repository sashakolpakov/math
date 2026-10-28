import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

/-! # Morphism Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor

noncomputable section

/-! Actual geometric pullback of family morphisms satisfies the strict functor laws and defines the family-morphism presheaf on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem geometricFamilyMorphismBaseChange_id {S : Scheme.{u}} {A B : Over S} (T : Over S)
    (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B) :
    MorphismBaseChange.geometricFamilyMorphismBaseChange (𝟙 T) p = p := by
  symm
  apply MorphismBaseChange.geometricFamilyMorphismBaseChange_unique
  rw [Single.ParameterFunctoriality.singleParameterBaseChangeMap_id, Single.ParameterFunctoriality.singleParameterBaseChangeMap_id, Category.comp_id, Category.id_comp]

theorem geometricFamilyMorphismBaseChange_composition {S : Scheme.{u}} {A B : Over S} {U T M : Over S}
    (f : U ⟶ T) (g : T ⟶ M)
    (p : (Over.pullback M.hom).obj A ⟶ (Over.pullback M.hom).obj B) :
    MorphismBaseChange.geometricFamilyMorphismBaseChange f (MorphismBaseChange.geometricFamilyMorphismBaseChange g p) =
      MorphismBaseChange.geometricFamilyMorphismBaseChange (f ≫ g) p := by
  apply MorphismBaseChange.geometricFamilyMorphismBaseChange_unique
  rw [Single.ParameterFunctoriality.singleParameterBaseChangeMap_composition, ← Category.assoc, MorphismBaseChange.geometricFamilyMorphismBaseChange_comp,
    Category.assoc, MorphismBaseChange.geometricFamilyMorphismBaseChange_comp, ← Category.assoc, ← Single.ParameterFunctoriality.singleParameterBaseChangeMap_composition]

def geometricFamilyMorphismFunctor {S : Scheme.{u}} (A B : Over S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (Over.pullback T.unop.hom).obj A ⟶ (Over.pullback T.unop.hom).obj B
  map f := TypeCat.ofHom (MorphismBaseChange.geometricFamilyMorphismBaseChange f.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro p
    exact geometricFamilyMorphismBaseChange_id T.unop p
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact (geometricFamilyMorphismBaseChange_composition g.unop f.unop p).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor
