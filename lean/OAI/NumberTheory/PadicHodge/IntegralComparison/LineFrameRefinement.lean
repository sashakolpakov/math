import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameCocycle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

/-! # Line Frame Refinement -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameRefinement

noncomputable section

/-! Refining a geometric trivializing map pulls back its actual
transition units. The proof keeps the native associativity comparisons
for pullback of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

universe u

variable {X Y Z W : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) (L : X.Modules)

def composition (p : W ⟶ Z) :
    (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback (g ≫ f)).obj L) ⟶
      (Scheme.Modules.pullback (p ≫ g)).obj ((Scheme.Modules.pullback f).obj L) :=
  (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackComp g f).inv.app L) ≫
    (Scheme.Modules.pullbackComp p g).hom.app ((Scheme.Modules.pullback f).obj L)

theorem composition_comp (p : W ⟶ Z) :
    composition f g L p ≫ (Scheme.Modules.pullbackComp (p ≫ g) f).hom.app L =
      (Scheme.Modules.pullbackComp p (g ≫ f)).hom.app L ≫
        (Scheme.Modules.pullbackCongr (Category.assoc p g f).symm).hom.app L := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp p (g ≫ f)).inv.app L)).mp
  simpa only [composition, Category.assoc, Iso.inv_hom_id_app_assoc] using
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents.modulePullback_associativity_components p g f L

theorem gluing (p q : W ⟶ Z) (h : p ≫ (g ≫ f) = q ≫ (g ≫ f)) :
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing (g ≫ f) p q h).hom.app L ≫ composition f g L q =
      composition f g L p ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (p ≫ g) (q ≫ g)
          ((Category.assoc p g f).trans (h.trans (Category.assoc q g f).symm))).hom.app L := by
  apply (cancel_mono ((Scheme.Modules.pullbackComp (q ≫ g) f).hom.app L)).mp
  simp only [Category.assoc]
  rw [composition_comp]
  simp only [AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc (composition f g L p), composition_comp]
  simp only [Category.assoc, AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.AssociativityComponents.modulePullbackCongr_hom_app, eqToHom_trans, Iso.inv_hom_id_app, Category.comp_id]

variable {L} (t : (Scheme.Modules.pullback f).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

def frame : (Scheme.Modules.pullback (g ≫ f)).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z :=
  ((Scheme.Modules.pullbackComp g f).app L).symm ≪≫
    (Scheme.Modules.pullback g).mapIso t ≪≫ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g

theorem frame_at (p : W ⟶ Z) :
    (LineFrame.Comparison.frameAt (g ≫ f) (frame f g t) p).hom =
      composition f g L p ≫ (LineFrame.Comparison.frameAt f t (p ≫ g)).hom := by
  have hu := congrArg Iso.hom (AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition.unitIso_comp p g)
  change (Scheme.Modules.pullback p).map (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom =
      (Scheme.Modules.pullbackComp p g).hom.app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (p ≫ g)).hom at hu
  change (Scheme.Modules.pullback p).map
    (((Scheme.Modules.pullbackComp g f).inv.app L ≫ (Scheme.Modules.pullback g).map t.hom) ≫
      (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom) ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom = _
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [hu]
  erw [← Category.assoc ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map t.hom)),
    (Scheme.Modules.pullbackComp p g).hom.naturality t.hom]
  simp only [composition, LineFrame.Comparison.frameAt, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]

theorem transitionIso (p q : W ⟶ Z) (h : p ≫ (g ≫ f) = q ≫ (g ≫ f)) :
    LineFrameCocycle.transitionIso (g ≫ f) (frame f g t) p q h =
      LineFrameCocycle.transitionIso f t (p ≫ g) (q ≫ g)
        ((Category.assoc p g f).trans (h.trans (Category.assoc q g f).symm)) := by
  apply Iso.ext
  apply (cancel_epi (LineFrame.Comparison.frameAt (g ≫ f) (frame f g t) p).hom).mp
  simp only [LineFrameCocycle.transitionIso, Iso.trans_hom, Iso.symm_hom,
    Iso.hom_inv_id_assoc]
  rw [frame_at, frame_at]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (LineFrame.Comparison.frameAt f t (q ≫ g)).hom)
      (gluing f g L p q h)).trans (Category.assoc _ _ _))

theorem transition (p q : W ⟶ Z) (h : p ≫ (g ≫ f) = q ≫ (g ≫ f)) :
    LineFrameCocycle.transition (g ≫ f) (frame f g t) p q h =
      LineFrameCocycle.transition f t (p ≫ g) (q ≫ g)
        ((Category.assoc p g f).trans (h.trans (Category.assoc q g f).symm)) :=
  congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso (transitionIso f g t p q h)

theorem transition_congr {f f' : Y ⟶ X} (h : f = f')
    {M : X.Modules} (t : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
    (p q : W ⟶ Y) (hpq : p ≫ f = q ≫ f) (hpq' : p ≫ f' = q ≫ f') :
    LineFrameCocycle.transition f' (((Scheme.Modules.pullbackCongr h).app M).symm ≪≫ t)
        p q hpq' = LineFrameCocycle.transition f t p q hpq := by
  subst f'
  change LineFrameCocycle.transition f ((Iso.refl _).symm ≪≫ t) p q hpq' = _
  simp only [Iso.refl_symm, Iso.refl_trans]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameRefinement
