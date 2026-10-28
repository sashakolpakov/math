import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ParameterPullbackNaturality

/-! # Morphism Composition Laws -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws

noncomputable section

/-! Geometric base change preserves composition of family morphisms and agrees with ordinary pullback on maps defined over the original base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {U T : Over S} {A B C : Over S}

theorem geometricFamilyMorphismBaseChange_map_comp (c : U ⟶ T)
    (f : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)
    (g : (Over.pullback T.hom).obj B ⟶ (Over.pullback T.hom).obj C) :
    MorphismBaseChange.geometricFamilyMorphismBaseChange c (f ≫ g) =
      MorphismBaseChange.geometricFamilyMorphismBaseChange c f ≫ MorphismBaseChange.geometricFamilyMorphismBaseChange c g := by
  simp only [MorphismBaseChange.geometricFamilyMorphismBaseChange, Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

theorem geometricFamilyMorphismBaseChange_original (c : U ⟶ T) (f : A ⟶ B) :
    MorphismBaseChange.geometricFamilyMorphismBaseChange c ((Over.pullback T.hom).map f) = (Over.pullback U.hom).map f := by
  symm
  exact MorphismBaseChange.geometricFamilyMorphismBaseChange_unique c _ _ (ParameterPullbackNaturality.singleParameterBaseChangeMap_natural c f)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws
