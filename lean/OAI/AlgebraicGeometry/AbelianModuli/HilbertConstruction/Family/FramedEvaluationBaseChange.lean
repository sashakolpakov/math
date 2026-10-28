import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.SectionPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.BaseChange

/-! # Framed Evaluation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedEvaluationBaseChange

noncomputable section

/-! Framed section evaluation commutes with an arbitrary base-change
square, using the actual pullback-composition and equality isomorphisms. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S T X Y : Scheme.{u}}

def familySectionFiberComparison (L : Line.Bundles.LineBundle X)
    (q : T ⟶ S) (f : Y ⟶ X) (x : S ⟶ X) (y : T ⟶ Y) (h : y ≫ f = q ≫ x) :
    ((L.pullback f).pullback y).sheaf ≅ ((L.pullback x).pullback q).sheaf :=
  (Scheme.Modules.pullbackComp y f).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr h).app L.sheaf ≪≫
      ((Scheme.Modules.pullbackComp q x).app L.sheaf).symm

theorem familySectionFiberComparison_section (L : Line.Bundles.LineBundle X)
    (q : T ⟶ S) (f : Y ⟶ X) (x : S ⟶ X) (y : T ⟶ Y) (h : y ≫ f = q ≫ x)
    (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.pullbackSection y (Ample.LineBundles.pullbackSection f a) ≫ (familySectionFiberComparison L q f x y h).hom =
      Ample.LineBundles.pullbackSection q (Ample.LineBundles.pullbackSection x a) := by
  calc
    _ = (Ample.LineBundles.pullbackSection y (Ample.LineBundles.pullbackSection f a) ≫
          (Scheme.Modules.pullbackComp y f).hom.app L.sheaf) ≫
        (Scheme.Modules.pullbackCongr h).hom.app L.sheaf ≫
          (Scheme.Modules.pullbackComp q x).inv.app L.sheaf := by
      simp only [familySectionFiberComparison, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rfl
    _ = Ample.LineBundles.pullbackSection (q ≫ x) a ≫ (Scheme.Modules.pullbackComp q x).inv.app L.sheaf := by
      rw [Global.SectionPullbackComposition.pullbackSection_composition, ← Category.assoc, Global.SectionPullbackComposition.pullbackSection_equality]
    _ = _ := by
      rw [← Global.SectionPullbackComposition.pullbackSection_composition q x a]
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact Category.comp_id _

def familySectionFrameBaseChange (L : Line.Bundles.LineBundle X)
    (q : T ⟶ S) (f : Y ⟶ X) (x : S ⟶ X) (y : T ⟶ Y) (h : y ≫ f = q ≫ x)
    (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) :
    ((L.pullback f).pullback y).sheaf ≅ Line.Bundles.structureModule T :=
  familySectionFiberComparison L q f x y h ≪≫
    (Scheme.Modules.pullback q).mapIso e ≪≫ Line.Bundles.structureModulePullbackIso q

theorem sectionFrameValue_pullback (q : T ⟶ S) {M : S.Modules}
    (e : M ≅ Line.Bundles.structureModule S) (a : Line.Bundles.structureModule S ⟶ M) :
    Frame.Coordinates.structureModuleEndValue T (Ample.LineBundles.pullbackSection q a ≫
      (Scheme.Modules.pullback q).map e.hom ≫ (Line.Bundles.structureModulePullbackIso q).hom) =
        q.appTop (Frame.Coordinates.structureModuleEndValue S (a ≫ e.hom)) := by
  rw [← Scalar.BaseChange.structureModuleEndValue_baseChange]
  congr 1
  simp only [Ample.LineBundles.pullbackSection, Functor.map_comp, Category.assoc]

theorem familyFramedSectionValue_baseChange (L : Line.Bundles.LineBundle X)
    (q : T ⟶ S) (f : Y ⟶ X) (x : S ⟶ X) (y : T ⟶ Y) (h : y ≫ f = q ≫ x)
    (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    FramedSectionEvaluation.familyFramedSectionValue (L.pullback f) y (familySectionFrameBaseChange L q f x y h e)
      (Ample.LineBundles.pullbackSection f a) = q.appTop (FramedSectionEvaluation.familyFramedSectionValue L x e a) := by
  change Frame.Coordinates.structureModuleEndValue T (Ample.LineBundles.pullbackSection y (Ample.LineBundles.pullbackSection f a) ≫
    ((familySectionFiberComparison L q f x y h).hom ≫
      ((Scheme.Modules.pullback q).map e.hom ≫ (Line.Bundles.structureModulePullbackIso q).hom))) = _
  rw [← Category.assoc, familySectionFiberComparison_section]
  exact sectionFrameValue_pullback q e (Ample.LineBundles.pullbackSection x a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedEvaluationBaseChange
