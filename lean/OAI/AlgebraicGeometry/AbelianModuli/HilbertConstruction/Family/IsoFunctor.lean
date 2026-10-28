import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.FamilyIsoBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismCompositionLaws

/-! # Iso Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoFunctor

noncomputable section

/-! Actual isomorphisms of two fixed family pullbacks form a functor, with natural maps recording the isomorphism and its inverse. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem geometricFamilyMorphismBaseChange_map_id
    {S : Scheme.{u}} {U T : Over S} (c : U ⟶ T) (A : Over S) :
    Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c (𝟙 ((Over.pullback T.hom).obj A)) =
      𝟙 ((Over.pullback U.hom).obj A) := by
  change (Single.ParameterBaseChange.singleParameterBaseChangeIso c A).hom ≫
    (Over.pullback c.left).map (𝟙 ((Over.pullback T.hom).obj A)) ≫
      (Single.ParameterBaseChange.singleParameterBaseChangeIso c A).inv = _
  rw [(Over.pullback c.left).map_id]
  simp only [Category.id_comp, Iso.hom_inv_id]

def familyIsoFunctor {S : Scheme.{u}} (A B : Over S) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (Over.pullback T.unop.hom).obj A ≅ (Over.pullback T.unop.hom).obj B
  map c := TypeCat.ofHom (Geometric.FamilyIsoBaseChange.geometricFamilyIsoBaseChange c.unop)
  map_id T := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Iso.ext
    exact Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_id T.unop e.hom
  map_comp c d := by
    apply ConcreteCategory.hom_ext
    intro e
    apply Iso.ext
    exact (Geometric.MorphismFunctor.geometricFamilyMorphismBaseChange_composition d.unop c.unop e.hom).symm

def familyIsoHom {S : Scheme.{u}} (A B : Over S) :
    familyIsoFunctor A B ⟶ Geometric.MorphismFunctor.geometricFamilyMorphismFunctor A B where
  app _ := TypeCat.ofHom Iso.hom
  naturality _ _ _ := rfl

def familyIsoInv {S : Scheme.{u}} (A B : Over S) :
    familyIsoFunctor A B ⟶ Geometric.MorphismFunctor.geometricFamilyMorphismFunctor B A where
  app T := TypeCat.ofHom (fun e : (Over.pullback T.unop.hom).obj A ≅ (Over.pullback T.unop.hom).obj B => e.inv)
  naturality T U c := by
    apply ConcreteCategory.hom_ext
    intro e
    change (Geometric.FamilyIsoBaseChange.geometricFamilyIsoBaseChange c.unop e).inv = Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c.unop e.inv
    simp only [Geometric.FamilyIsoBaseChange.geometricFamilyIsoBaseChange, Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange,
      Iso.trans_inv, Iso.symm_inv, Category.assoc]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.IsoFunctor
