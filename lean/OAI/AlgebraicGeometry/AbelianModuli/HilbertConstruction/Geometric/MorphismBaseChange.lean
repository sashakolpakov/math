import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality

/-! # Morphism Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange

noncomputable section

/-! Actual morphisms between original family pullbacks have a geometric base-change operation characterized by its Cartesian square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {U T : Over S} {A B : Over S}
variable (f : U ⟶ T) (p : (Over.pullback T.hom).obj A ⟶ (Over.pullback T.hom).obj B)

def geometricFamilyMorphismBaseChange : (Over.pullback U.hom).obj A ⟶ (Over.pullback U.hom).obj B :=
  (Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ≫ (Over.pullback f.left).map p ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).inv

theorem geometricFamilyMorphismBaseChange_comp :
    (geometricFamilyMorphismBaseChange f p).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f B =
      Single.ParameterBaseChange.singleParameterBaseChangeMap f A ≫ p.left := by
  have hp : ((Over.pullback f.left).map p).left ≫ pullback.fst ((Over.pullback T.hom).obj B).hom f.left =
      pullback.fst ((Over.pullback T.hom).obj A).hom f.left ≫ p.left := pullback.lift_fst _ _ _
  change ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom.left ≫
      (((Over.pullback f.left).map p).left ≫ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).inv.left)) ≫
        Single.ParameterBaseChange.singleParameterBaseChangeMap f B = _
  simp only [Category.assoc]
  rw [Single.ParameterFunctoriality.singleParameterBaseChangeIso_inv_comp, hp, ← Category.assoc, Single.ParameterFunctoriality.singleParameterBaseChangeIso_hom_fst]

theorem geometricFamilyMorphismBaseChange_unique
    (q : (Over.pullback U.hom).obj A ⟶ (Over.pullback U.hom).obj B)
    (hq : q.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap f B = Single.ParameterBaseChange.singleParameterBaseChangeMap f A ≫ p.left) :
    q = geometricFamilyMorphismBaseChange f p := by
  apply Over.OverMorphism.ext
  apply (Single.ParameterBaseChange.singleParameterBaseChangeMap_isPullback f B).hom_ext
  · exact hq.trans (geometricFamilyMorphismBaseChange_comp f p).symm
  · exact q.w.trans (geometricFamilyMorphismBaseChange f p).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.MorphismBaseChange
