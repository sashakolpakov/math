import OAI.AlgebraicGeometry.PELModuli.IntegralModel.KernelPairDescentMorphisms
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.GlobalSquareFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms

/-! # Ordinary Framed Datum -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryFramedDatum

noncomputable section

/-! An actual invariant frame on a kernel-pair presentation identifies
the complete ordinary datum with the trivial-line datum. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem ordinaryBaseDatum_hom {X Y T : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f M).hom q
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app M ≫
        (Scheme.Modules.pullbackComp y f ≪≫ Scheme.Modules.pullbackCongr hy).inv.app M := by
  change (Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f M x q hx).hom ≫
    (Picard.PoincareBundle.PullbackFiberComposition.fiberIsoTo Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f M y q hy).inv = _
  rw [Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq, Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.fiberIsoTo_eq]
  rfl

theorem structureFrame_composite {X Y T : Scheme.{0}} (f : X ⟶ Y)
    (q : T ⟶ Y) (x : T ⟶ X) (hx : x ≫ f = q) :
    (Scheme.Modules.pullbackComp x f ≪≫ Scheme.Modules.pullbackCongr hx).hom.app
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom =
      ((Scheme.Modules.pullback x).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom := by
  cases hx
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl,
    LineBundle.GlobalSquareFrame.structureModulePullbackIso_eq]
  exact congrArg CategoryTheory.Iso.hom (RepresentationTheory.Theta.Geometric.Pullback.FrameComposition.pullbackUnitIso_comp x f)

theorem canonicalStructureDatum_frame {X Y T : Scheme.{0}} (f : X ⟶ Y)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)).hom q
        (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
      ((Scheme.Modules.pullback y).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).hom =
      ((Scheme.Modules.pullback x).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom := by
  rw [ordinaryBaseDatum_hom, ← structureFrame_composite f q y hy]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact structureFrame_composite f q x hx

theorem framedDatum_pair_compatible {X Y T : Scheme.{0}} (f : X ⟶ Y)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (he : D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
      ((Scheme.Modules.pullback y).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).hom =
        ((Scheme.Modules.pullback x).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso x).hom) :
    (Scheme.Modules.pullback x).map (e ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm).hom ≫
        (Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)).hom q
          (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy =
      D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
        (Scheme.Modules.pullback y).map (e ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm).hom := by
  apply (cancel_mono ((Scheme.Modules.pullback y).mapIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f) ≪≫
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso y).hom).mp
  simp only [Category.assoc]
  rw [canonicalStructureDatum_frame]
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Functor.mapIso_hom,
    Category.assoc, Iso.map_inv_hom_id_assoc] using he.symm

def framedKernelPairDatumIso {X Y R : Scheme.{0}} (f : X ⟶ Y) (s t : R ⟶ X)
    (hk : IsKernelPair f s t)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : D.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl ≫
      ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom =
        ((Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s).hom) :
    D ≅ Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) := by
  let a := KernelPairDescentMorphisms.kernelPair_descentHom Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f s t hk D
    (Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y))
    (e ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm).hom
    (framedDatum_pair_compatible f D e (t ≫ f) s t hk.w rfl he)
  have : IsIso (a.hom PUnit.unit) := (e ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm).isIso_hom
  exact Picard.PoincareBundle.DescentComponentIsomorphisms.isoOfComponent Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f a

theorem exists_framedKernelPairDatumIso {X Y R : Scheme.{0}} (f : X ⟶ Y) (s t : R ⟶ X)
    (hk : IsKernelPair f s t)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : D.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl ≫
      ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom =
        ((Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s).hom) :
    Nonempty (D ≅ Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) := ⟨framedKernelPairDatumIso f s t hk D e he⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryFramedDatum
