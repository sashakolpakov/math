import OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom
import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition

/-! # Line Frame Cocycle -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameCocycle

noncomputable section

/-! Local frames of an actual module sheaf give unit-valued transition
functions. Their cocycle law follows from the canonical pullback
comparisons; it is not an extra condition on the line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar

universe u

theorem gluing_refl {X Y T : Scheme.{u}} (f : Y ⟶ X) (p : T ⟶ Y) :
    AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p p rfl = Iso.refl _ := by
  simp [AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing, Scheme.Modules.pullbackCongr]

theorem gluing_trans {X Y T : Scheme.{u}} (f : Y ⟶ X)
    (p q r : T ⟶ Y) (hpq : p ≫ f = q ≫ f) (hqr : q ≫ f = r ≫ f) :
    AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q hpq ≪≫ AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f q r hqr =
      AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p r (hpq.trans hqr) := by
  have h : Scheme.Modules.pullbackCongr hpq ≪≫ Scheme.Modules.pullbackCongr hqr =
      Scheme.Modules.pullbackCongr (hpq.trans hqr) := by
    simp [Scheme.Modules.pullbackCongr]
  calc
    _ = Scheme.Modules.pullbackComp p f ≪≫
        (Scheme.Modules.pullbackCongr hpq ≪≫ Scheme.Modules.pullbackCongr hqr) ≪≫
          (Scheme.Modules.pullbackComp r f).symm := by
      apply Iso.ext
      simp [AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing]
    _ = _ := by rw [h]; rfl

theorem baseDatum_hom {X Y T : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    (AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f L).hom (q ≫ f)
      (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q h rfl =
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L := by
  change (AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f L p (q ≫ f) h).hom ≫
    (AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo
      AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f L q (q ≫ f) rfl).inv = _
  rw [AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq, AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rfl

theorem gluing_pullback {X Y T T' : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) (g : T' ⟶ T) :
    (Scheme.Modules.pullback g).map ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L) ≫
        (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback f).obj L) =
      (Scheme.Modules.pullbackComp g p).hom.app ((Scheme.Modules.pullback f).obj L) ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (g ≫ p) (g ≫ q) (by simp only [Category.assoc, h])).hom.app L := by
  have hd := (AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f L).pullHom_hom g
    (q ≫ f) ((g ≫ q) ≫ f) (Category.assoc _ _ _).symm
    (i₁ := PUnit.unit) (i₂ := PUnit.unit) p q h rfl (g ≫ p) (g ≫ q) rfl rfl
  rw [baseDatum_hom, baseDatum_hom, AlgebraicGeometry.Picard.PoincareBundle.Geometric.PullHom.pullHom_eq] at hd
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl] at hd
  change (Scheme.Modules.pullbackComp g p).inv.app ((Scheme.Modules.pullback f).obj L) ≫
    (Scheme.Modules.pullback g).map ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L) ≫
      (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback f).obj L) = _ at hd
  have he := congrArg
    (fun z => (Scheme.Modules.pullbackComp g p).hom.app ((Scheme.Modules.pullback f).obj L) ≫ z) hd
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using he

theorem unitOfIso_trans {T : Scheme.{u}}
    (e d : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) :
    AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso (e ≪≫ d) =
      AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso e * AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso d := by
  apply Units.ext
  exact AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar_comp e.hom d.hom

theorem scalarEnd_unitOfIso {T : Scheme.{u}} (e : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) :
    AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso e).val = e.hom := by
  apply AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar_injective
  rw [LineTrivializationCoboundary.scalar_value]
  rfl

variable {X Y T : Scheme.{u}} (f : Y ⟶ X) {L : X.Modules}
  (t : (Scheme.Modules.pullback f).obj L ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)

theorem frame_pullback {T' : Scheme.{u}} (g : T' ⟶ T) (p : T ⟶ Y) :
    (Scheme.Modules.pullback g).map (LineFrame.Comparison.frameAt f t p).hom ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom =
      (Scheme.Modules.pullbackComp g p).hom.app ((Scheme.Modules.pullback f).obj L) ≫
        (LineFrame.Comparison.frameAt f t (g ≫ p)).hom := by
  have hu := congrArg Iso.hom (AlgebraicGeometry.Picard.PoincareBundle.StructureUnitComposition.unitIso_comp g p)
  change (Scheme.Modules.pullback g).map (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom =
      (Scheme.Modules.pullbackComp g p).hom.app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
        (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (g ≫ p)).hom at hu
  change (Scheme.Modules.pullback g).map
      ((Scheme.Modules.pullback p).map t.hom ≫ (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, hu, ← Category.assoc]
  erw [(Scheme.Modules.pullbackComp g p).hom.naturality t.hom]
  simp only [LineFrame.Comparison.frameAt, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc]

def transitionIso (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T :=
  (LineFrame.Comparison.frameAt f t p).symm ≪≫
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).app L ≪≫ LineFrame.Comparison.frameAt f t q

def transition (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) : Γ(T, ⊤)ˣ :=
  AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso (transitionIso f t p q h)

theorem normalized (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫ (LineFrame.Comparison.frameAt f t q).hom =
      (LineFrame.Comparison.frameAt f t p).hom ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) (transition f t p q h).val := by
  rw [transition, scalarEnd_unitOfIso]
  simp [transitionIso]

theorem transition_refl (p : T ⟶ Y) : transition f t p p rfl = 1 := by
  apply Units.ext
  change AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar (transitionIso f t p p rfl).hom = 1
  simp [transitionIso, gluing_refl]

theorem transition_unit (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    transition f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) p q h = 1 := by
  have hu : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) ≫
      (LineFrame.Comparison.frameAt f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) q).hom =
        (LineFrame.Comparison.frameAt f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) p).hom := by
    simpa only [LineFrame.Comparison.frameAt, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc] using (AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing.unit_gluing f p q h).symm
  have he : (transitionIso f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) p q h).hom = 𝟙 _ := by
    change ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).app (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom ≫
      (LineFrame.Comparison.frameAt f (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) q).hom = _ at hu
    simp only [transitionIso, Iso.trans_hom, Iso.symm_hom]
    rw [hu, Iso.inv_hom_id]
  apply Units.ext
  exact congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar he

theorem transition_cocycle (p q r : T ⟶ Y)
    (hpq : p ≫ f = q ≫ f) (hqr : q ≫ f = r ≫ f) :
    transition f t p q hpq * transition f t q r hqr =
      transition f t p r (hpq.trans hqr) := by
  change AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso (transitionIso f t p q hpq) *
      AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso (transitionIso f t q r hqr) = _
  rw [← unitOfIso_trans]
  apply congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.unitOfIso
  apply Iso.ext
  have hG : (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q hpq).hom.app L ≫
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f q r hqr).hom.app L =
        (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p r (hpq.trans hqr)).hom.app L :=
    congrArg (fun e => e.hom.app L) (gluing_trans f p q r hpq hqr)
  change ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q hpq).app L).hom ≫ ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f q r hqr).app L).hom =
    ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p r (hpq.trans hqr)).app L).hom at hG
  simp only [transitionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.hom_inv_id_assoc, ← hG]

theorem transition_restrict {T' : Scheme.{u}} (g : T' ⟶ T)
    (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    Units.map g.appTop.hom.toMonoidHom (transition f t p q h) =
      transition f t (g ≫ p) (g ≫ q) (by simp only [Category.assoc, h]) := by
  let F := Scheme.Modules.pullback g
  let U := (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom
  let h' : (g ≫ p) ≫ f = (g ≫ q) ≫ f := by simp only [Category.assoc, h]
  let d := transition f t p q h
  let d' := transition f t (g ≫ p) (g ≫ q) h'
  have he : (F.map (LineFrame.Comparison.frameAt f t p).hom ≫ U) ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T') (g.appTop d.val) =
      (F.map (LineFrame.Comparison.frameAt f t p).hom ≫ U) ≫
        AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T') d'.val := by
    calc
      _ = F.map ((LineFrame.Comparison.frameAt f t p).hom ≫
          AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T) d.val) ≫ U := by
        rw [Functor.map_comp, AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_pullback]
        simp only [Category.assoc]
        exact congrArg (fun k => F.map (LineFrame.Comparison.frameAt f t p).hom ≫ k)
          (AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd_naturality U (g.appTop d.val)).symm
      _ = F.map ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L ≫
          (LineFrame.Comparison.frameAt f t q).hom) ≫ U := by
        rw [normalized]
      _ = F.map ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f p q h).hom.app L) ≫
          (Scheme.Modules.pullbackComp g q).hom.app ((Scheme.Modules.pullback f).obj L) ≫
            (LineFrame.Comparison.frameAt f t (g ≫ q)).hom := by
        rw [Functor.map_comp, Category.assoc, frame_pullback]
      _ = (Scheme.Modules.pullbackComp g p).hom.app ((Scheme.Modules.pullback f).obj L) ≫
          ((AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (g ≫ p) (g ≫ q) h').hom.app L ≫
            (LineFrame.Comparison.frameAt f t (g ≫ q)).hom) := by
        rw [← Category.assoc, gluing_pullback, Category.assoc]
      _ = (Scheme.Modules.pullbackComp g p).hom.app ((Scheme.Modules.pullback f).obj L) ≫
          (LineFrame.Comparison.frameAt f t (g ≫ p)).hom ≫
            AlgebraicGeometry.Isogenies.NeighborCounting.ModuleScalar.scalarEnd (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T') d'.val := by
        rw [normalized]
      _ = _ := by
        rw [frame_pullback]
        simp only [Category.assoc]
  have hs := (cancel_epi (F.map (LineFrame.Comparison.frameAt f t p).hom ≫ U)).mp he
  apply Units.ext
  change g.appTop d.val = d'.val
  simpa only [LineTrivializationCoboundary.scalar_value] using
    congrArg AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits.scalar hs

theorem comparison {M : X.Modules}
    (s : (Scheme.Modules.pullback f).obj M ≅ AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (e : L ≅ M)
    (p q : T ⟶ Y) (h : p ≫ f = q ≫ f) :
    transition f t p q h / transition f s p q h =
      Units.map p.appTop.hom.toMonoidHom (LineFrame.Comparison.correction f t s e) /
        Units.map q.appTop.hom.toMonoidHom (LineFrame.Comparison.correction f t s e) :=
  LineFrame.Comparison.quotient_equation f t s e p q h
    (transition f t p q h) (transition f s p q h)
    (normalized f t p q h) (normalized f s p q h)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LineFrameCocycle
