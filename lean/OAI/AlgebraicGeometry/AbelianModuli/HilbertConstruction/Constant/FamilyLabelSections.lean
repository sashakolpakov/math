import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.BaseChangeLabels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Single.ParameterFunctoriality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.PointSectionNaturality

/-! # Family Label Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyLabelSections

noncomputable section

/-! The ordered sections of a constant family commute with geometric parameter base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} (I : Type u)

def constantFamilyLabelSection (T : Over S) (i : I) :
    𝟙_ (Over T.left) ⟶ (Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I) :=
  ConstantScheme.Morphisms.constantSchemeLabelPoint T.left I i ≫ (BaseChange.constantSchemeBaseChangeIso T.hom I).hom

theorem constantFamilyLabelSection_fst (T : Over S) (i : I) :
    (constantFamilyLabelSection I T i).left ≫ pullback.fst (ConstantScheme.Iff.constantScheme S I).hom T.hom =
      T.hom ≫ (ConstantScheme.Morphisms.constantSchemeLabelPoint S I i).left :=
  BaseChangeLabels.constantSchemeBaseChangeIso_label_fst T.hom I i

theorem constantFamilyLabelSection_natural {U T : Over S} (c : U ⟶ T) (i : I) :
    (constantFamilyLabelSection I U i).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c (ConstantScheme.Iff.constantScheme S I) =
      c.left ≫ (constantFamilyLabelSection I T i).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, Single.ParameterBaseChange.singleParameterBaseChangeMap_comp, constantFamilyLabelSection_fst,
      Category.assoc, constantFamilyLabelSection_fst, ← Category.assoc, c.w]
  · have hc : Single.ParameterBaseChange.singleParameterBaseChangeMap c (ConstantScheme.Iff.constantScheme S I) ≫
        ((Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I)).hom =
      ((Over.pullback U.hom).obj (ConstantScheme.Iff.constantScheme S I)).hom ≫ c.left :=
        Single.ParameterFunctoriality.singleParameterBaseChangeMap_over c _
    change ((constantFamilyLabelSection I U i).left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c (ConstantScheme.Iff.constantScheme S I)) ≫
        ((Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I)).hom =
      (c.left ≫ (constantFamilyLabelSection I T i).left) ≫
        ((Over.pullback T.hom).obj (ConstantScheme.Iff.constantScheme S I)).hom
    rw [Category.assoc, hc, ← Category.assoc, (constantFamilyLabelSection I U i).w,
      Category.assoc, (constantFamilyLabelSection I T i).w]
    exact (Category.id_comp c.left).trans (Category.comp_id c.left).symm

theorem familySectionPoints_natural {A U T : Over S} (c : U ⟶ T)
    (sU : 𝟙_ (Over U.left) ⟶ (Over.pullback U.hom).obj A)
    (sT : 𝟙_ (Over T.left) ⟶ (Over.pullback T.hom).obj A)
    (h : sU.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c A = c.left ≫ sT.left) :
    (Family.PointSectionEquivalence.familyPointSectionEquiv A U).symm sU = c ≫ (Family.PointSectionEquivalence.familyPointSectionEquiv A T).symm sT := by
  apply Over.OverMorphism.ext
  change sU.left ≫ pullback.fst A.hom U.hom = c.left ≫ (sT.left ≫ pullback.fst A.hom T.hom)
  calc
    _ = (sU.left ≫ Single.ParameterBaseChange.singleParameterBaseChangeMap c A) ≫ pullback.fst A.hom T.hom :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun q => sU.left ≫ q) (Single.ParameterBaseChange.singleParameterBaseChangeMap_comp c A))).symm
    _ = (c.left ≫ sT.left) ≫ pullback.fst A.hom T.hom :=
      congrArg (fun q : U.left ⟶ ((Over.pullback T.hom).obj A).left => q ≫ pullback.fst A.hom T.hom) h
    _ = _ := Category.assoc _ _ _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.FamilyLabelSections
