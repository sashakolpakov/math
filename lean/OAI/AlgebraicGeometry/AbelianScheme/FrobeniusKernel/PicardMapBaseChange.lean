import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.BaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Isogeny.BaseChange

/-! # Picard Map Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback

noncomputable section

/-! Canonical Picard pullback commutes with base change. The
comparison is induced by the original family product maps and the
native homogeneous Picard representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Functor (familyMap)

variable {S S' : Scheme.{u}} {X Y : Over S} (p : X ⟶ Y) (f : S' ⟶ S)

theorem familyMap_eq_whisker (T : Over S) : Picard.PoincareBundle.Functor.familyMap p T = (T ◁ p).left := by
  simp only [Picard.PoincareBundle.Functor.familyMap, tensorHom_def, id_whiskerRight, Category.id_comp]

theorem familyBaseChangeIso_map_hom (T : Over S') :
    Picard.PoincareBundle.Functor.familyMap ((Over.pullback f).map p) T ≫ (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso Y f T).hom =
      (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso X f T).hom ≫ Picard.PoincareBundle.Functor.familyMap p ((Over.map f).obj T) := by
  simp only [familyMap_eq_whisker]
  apply CategoryTheory.Limits.pullback.hom_ext
  · have hL : (T ◁ (Over.pullback f).map p).left ≫
        CategoryTheory.Limits.pullback.fst T.hom (CategoryTheory.Limits.pullback.snd Y.hom f) =
      CategoryTheory.Limits.pullback.fst T.hom (CategoryTheory.Limits.pullback.snd X.hom f) :=
        Over.whiskerLeft_left_fst _
    have hR : (((Over.map f).obj T) ◁ p).left ≫
        CategoryTheory.Limits.pullback.fst (T.hom ≫ f) Y.hom =
      CategoryTheory.Limits.pullback.fst (T.hom ≫ f) X.hom := Over.whiskerLeft_left_fst _
    simp only [Category.assoc, AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_fst, hL, hR]
  · have hL : (T ◁ (Over.pullback f).map p).left ≫
        CategoryTheory.Limits.pullback.snd T.hom (CategoryTheory.Limits.pullback.snd Y.hom f) =
      CategoryTheory.Limits.pullback.snd T.hom (CategoryTheory.Limits.pullback.snd X.hom f) ≫
        ((Over.pullback f).map p).left := Over.whiskerLeft_left_snd _
    have hR : (((Over.map f).obj T) ◁ p).left ≫
        CategoryTheory.Limits.pullback.snd (T.hom ≫ f) Y.hom =
      CategoryTheory.Limits.pullback.snd (T.hom ≫ f) X.hom ≫ p.left := Over.whiskerLeft_left_snd _
    have hp : ((Over.pullback f).map p).left ≫ CategoryTheory.Limits.pullback.fst Y.hom f =
        CategoryTheory.Limits.pullback.fst X.hom f ≫ p.left :=
      CategoryTheory.Limits.pullback.lift_fst _ _ _
    simp only [Category.assoc, AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd, hR]
    rw [← Category.assoc, hL, Category.assoc, hp]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ p.left) (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd X f T).symm).trans
        (Category.assoc _ _ _))

theorem familyBaseChangeIso_map_inv (T : Over S') :
    (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso X f T).inv ≫ Picard.PoincareBundle.Functor.familyMap ((Over.pullback f).map p) T =
      Picard.PoincareBundle.Functor.familyMap p ((Over.map f).obj T) ≫ (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso Y f T).inv := by
  apply (cancel_epi (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso X f T).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← familyBaseChangeIso_map_hom p f T]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {g h : ℕ} {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h S}
variable (p : A.scheme ⟶ B.scheme) [IsMonHom p]

def nativeBaseChangeMap : (A.pullback f).scheme ⟶ (B.pullback f).scheme :=
  (Over.pullback f).map p

instance nativeBaseChangeMap_isMonHom : IsMonHom (nativeBaseChangeMap f p) := by
  let : GrpObj ((Over.pullback f).obj A.scheme) := Functor.grpObjObj
  let : GrpObj ((Over.pullback f).obj B.scheme) := Functor.grpObjObj
  exact Functor.map.instIsMonHom (F := Over.pullback f) (f := p) A.scheme B.scheme

theorem pullbackHomogeneousPresheaf_baseChange :
    PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf (nativeBaseChangeMap f p) ≫
      (A.homogeneousPicardPresheafBaseChangeIso f).hom =
    (B.homogeneousPicardPresheafBaseChangeIso f).hom ≫
      Functor.whiskerLeft (Over.map f).op (PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf p) := by
  apply NatTrans.ext
  funext T
  apply ConcreteCategory.ext_apply
  intro z
  apply Subtype.ext
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T.unop).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap ((Over.pullback f).map p) T.unop) z.val) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Picard.PoincareBundle.Functor.familyMap p ((Over.map f).obj T.unop))
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme f T.unop).inv z.val)
  exact (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f T.unop).inv
    (Picard.PoincareBundle.Functor.familyMap ((Over.pullback f).map p) T.unop) z.val).symm.trans
      ((congrArg (fun r => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass r z.val)
        (familyBaseChangeIso_map_inv p f T.unop)).trans
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp (Picard.PoincareBundle.Functor.familyMap p ((Over.map f).obj T.unop))
            (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso B.scheme f T.unop).inv z.val))

theorem map_square_comp_naturality {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : E ⥤ C) (H : E ⥤ D) (comparison : G ⋙ F ⟶ H)
    {X Y : C} {X' Y' : E} (a : X ⟶ Y) (b : X' ⟶ Y')
    (i : X ⟶ G.obj X') (j : Y ⟶ G.obj Y') (h : a ≫ j = i ≫ G.map b) :
    F.map a ≫ (F.map j ≫ comparison.app Y') = (F.map i ≫ comparison.app X') ≫ H.map b := by
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  exact (congrArg (fun r => F.map i ≫ r) (comparison.naturality b)).trans
    (Category.assoc _ _ _).symm

theorem pullbackHomogeneousSheaf_baseChange :
    PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf (nativeBaseChangeMap f p) ≫
      (A.homogeneousPicardSheafBaseChangeIso f).hom =
    (B.homogeneousPicardSheafBaseChangeIso f).hom ≫
      (Scheme.fppfTopology.overMapPullback (Type (u + 1)) f).map (PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousSheaf p) := by
  exact map_square_comp_naturality
    (presheafToSheaf (Scheme.fppfTopology.over S') (Type (u + 1))) _ _
    (((Over.map f).pushforwardContinuousSheafificationCompatibility (Type (u + 1))
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom)
    (PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf (nativeBaseChangeMap f p)) (PicardPullback.Construction.IntrinsicPicardPullback.pullbackHomogeneousPresheaf p)
    (B.homogeneousPicardPresheafBaseChangeIso f).hom
    (A.homogeneousPicardPresheafBaseChangeIso f).hom
    (pullbackHomogeneousPresheaf_baseChange f p)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardMapBaseChange.Construction.IntrinsicPicardPullback
