import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyLabelSections

/-! # Family Morphism Labels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyMorphismLabels

noncomputable section

/-! Morphisms from a base-changed constant family are naturally equivalent to ordered tuples of points of the target family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def overIsoSourceHomEquiv {S : Scheme.{u}} {X Y Z : Over S} (e : X ≅ Y) :
    (Y ⟶ Z) ≃ (X ⟶ Z) where
  toFun f := e.hom ≫ f
  invFun f := e.inv ≫ f
  left_inv _ := Iso.inv_hom_id_assoc _ _
  right_inv _ := Iso.hom_inv_id_assoc _ _

variable {S : Scheme.{u}} (A : Over S) (I : Type u)

def constantFamilyMorphismLabelsEquiv (T : Over S) :
    ((Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶ (Over.pullback T.hom).obj A) ≃ (I → (T ⟶ A)) :=
  (overIsoSourceHomEquiv (BaseChange.constantSchemeBaseChangeIso T.hom I)).trans
    ((ConstantScheme.Morphisms.constantSchemeMorphismEquiv T.left I ((Over.pullback T.hom).obj A)).trans
      (Equiv.piCongrRight (fun _ => (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm)))

theorem constantFamilyMorphismLabelsEquiv_apply (T : Over S)
    (p : (Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶ (Over.pullback T.hom).obj A) (i : I) :
    constantFamilyMorphismLabelsEquiv A I T p i =
      (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm (FamilyLabelSections.constantFamilyLabelSection I T i ≫ p) :=
  congrArg (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm
    (Category.assoc (ConstantScheme.Morphisms.constantSchemeLabelPoint T.left I i) (BaseChange.constantSchemeBaseChangeIso T.hom I).hom p).symm

theorem constantFamilyMorphismLabelsEquiv_natural {U T : Over S} (c : U ⟶ T)
    (p : (Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) ⟶ (Over.pullback T.hom).obj A) (i : I) :
    constantFamilyMorphismLabelsEquiv A I U (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p) i =
      c ≫ constantFamilyMorphismLabelsEquiv A I T p i := by
  rw [constantFamilyMorphismLabelsEquiv_apply, constantFamilyMorphismLabelsEquiv_apply]
  apply FamilyLabelSections.familySectionPoints_natural
  change ((FamilyLabelSections.constantFamilyLabelSection I U i).left ≫ (Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange c p).left) ≫
      Single.ParameterBaseChange.singleParameterBaseChangeMap c A = c.left ≫ ((FamilyLabelSections.constantFamilyLabelSection I T i).left ≫ p.left)
  rw [Category.assoc, Geometric.MorphismBaseChange.geometricFamilyMorphismBaseChange_comp, ← Category.assoc,
    FamilyLabelSections.constantFamilyLabelSection_natural, Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyMorphismLabels
