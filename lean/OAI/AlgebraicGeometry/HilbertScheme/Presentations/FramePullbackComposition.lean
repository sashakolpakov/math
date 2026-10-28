import OAI.AlgebraicGeometry.HilbertScheme.Presentations.StructureFrameComposition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FrameTransitionPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion

/-! # Frame Pullback Composition -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FramePullbackComposition

noncomputable section

/-! Pulling a frame through two scheme morphisms agrees with direct
pullback, including the canonical source identifications. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityFusion

universe u
variable {W X Y Z : Scheme.{u}}

theorem pullbackFrame_change_source (a : X ⟶ Y) {M N : Y.Modules}
    (h : M ≅ N) (e : N ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    FrameTransitionPullback.pullbackFrame a (h ≪≫ e) = (Scheme.Modules.pullback a).mapIso h ≪≫ FrameTransitionPullback.pullbackFrame a e := by
  apply Iso.ext
  simp only [FrameTransitionPullback.pullbackFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]

theorem pullbackFrame_comp (a : X ⟶ Y) (b : Y ⟶ Z) {M : Z.Modules}
    (e : M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) :
    FrameTransitionPullback.pullbackFrame a (FrameTransitionPullback.pullbackFrame b e) =
      (Scheme.Modules.pullbackComp a b).app M ≪≫ FrameTransitionPullback.pullbackFrame (a ≫ b) e := by
  apply Iso.ext
  simp only [FrameTransitionPullback.pullbackFrame, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [← StructureFrameComposition.structureFrame_pullback_comp]
  have hn : (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map e.hom) ≫
      (Scheme.Modules.pullbackComp a b).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) =
        (Scheme.Modules.pullbackComp a b).hom.app M ≫ (Scheme.Modules.pullback (a ≫ b)).map e.hom :=
    (Scheme.Modules.pullbackComp a b).hom.naturality e.hom
  simpa only [Category.assoc] using! congrArg (fun k => k ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (a ≫ b)).hom) hn

def refineFrame (a : X ⟶ Y) (b : Y ⟶ Z) {M : Z.Modules}
    (e : (Scheme.Modules.pullback b).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    (Scheme.Modules.pullback (a ≫ b)).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X :=
  ((Scheme.Modules.pullbackComp a b).app M).symm ≪≫ FrameTransitionPullback.pullbackFrame a e

theorem refineFrame_assoc (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) {M : Z.Modules}
    (e : (Scheme.Modules.pullback c).obj M ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) :
    refineFrame a (b ≫ c) (refineFrame b c e) =
      (Scheme.Modules.pullbackCongr (Category.assoc a b c).symm).app M ≪≫
        refineFrame (a ≫ b) c e := by
  have h := AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents.modulePullback_associativity_components a b c M
  have h' := congrArg (fun k => k ≫ (Scheme.Modules.pullbackComp (a ≫ b) c).inv.app M) h
  simp only [← Category.assoc] at h'
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_app] at h'
  simp only [Functor.comp_obj, Category.comp_id] at h'
  unfold refineFrame
  rw [pullbackFrame_change_source, pullbackFrame_comp]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simpa only [Category.assoc] using! congrArg (fun k => k ≫ (FrameTransitionPullback.pullbackFrame (a ≫ b) e).hom) h'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FramePullbackComposition
