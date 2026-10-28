import OAI.AlgebraicGeometry.PELModuli.IntegralModel.OrdinaryFramedDatum
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Line.IsoFromDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.OverlapPullback

/-! # Framed Line Recovery -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery

noncomputable section

section

/-! An invariant actual frame trivializes a specified recovered line,
using native morphism compatibility and line-descent uniqueness. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem iso_inverse_square {C : Type*} [Category* C] {A B X Y : C}
    (e : A ≅ B) (f : X ≅ Y) (a : A ⟶ X) (b : B ⟶ Y)
    (h : e.hom ≫ b = a ≫ f.hom) : e.inv ≫ a = b ≫ f.inv := by
  have hh := congrArg (fun q => e.inv ≫ q ≫ f.inv) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh.symm

theorem framedUnitRecovery_compatible {X Y R : Scheme.{0}} (f : X ⟶ Y) (s t : R ⟶ X)
    (hk : IsKernelPair f s t)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : D.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl ≫
      ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom =
        ((Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s).hom) :
    (Scheme.Modules.pullback (pullback.fst f f)).map
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm).hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map
          (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm).hom := by
  let E := Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum f (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)
  let c := e ≪≫ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).symm
  have hc := OrdinaryFramedDatum.framedDatum_pair_compatible f D e (t ≫ f) s t hk.w rfl he
  have ha := KernelPairDescentMorphisms.kernelPair_descent_compatible Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks f s t hk D E c.hom hc
    (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f) pullback.condition rfl
  have hb := iso_inverse_square ((Scheme.Modules.pullback (pullback.fst f f)).mapIso c)
    ((Scheme.Modules.pullback (pullback.snd f f)).mapIso c)
    (D.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (pullback.fst f f) (pullback.snd f f) pullback.condition rfl)
    (E.hom (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (pullback.fst f f) (pullback.snd f f) pullback.condition rfl) ha
  change (Scheme.Modules.pullback (pullback.fst f f)).map
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm).hom ≫
    (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f E).hom ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map
          (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm).hom at hb
  rw [Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary.baseDatum_gluing] at hb
  exact hb

theorem recoveredLine_trivial_of_frame {X Y R : Scheme.{0}} (f : X ⟶ Y)
    [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]
    (s t : R ⟶ X) (hk : IsKernelPair f s t)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : D.hom (t ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hk.w rfl ≫
      ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom =
        ((Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s).hom)
    (P : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y) (r : (P.pullback f).sheaf ≅ D.obj PUnit.unit)
    (hr : (Scheme.Modules.pullback (pullback.fst f f)).map r.hom ≫
      (Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
        (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
          pullback.condition).hom.app P.sheaf ≫ (Scheme.Modules.pullback (pullback.snd f f)).map r.hom) :
    Nonempty (P.sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) := by
  have hD : Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit) := (Picard.PoincareBundle.Line.Bundles.isLine_unit X).of_iso e.symm
  obtain ⟨a, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (⟨P.sheaf, P.locallyTrivial⟩ : Picard.PoincareBundle.Line.Bundles.LineBundle Y) r hr
  obtain ⟨b, _, _⟩ := Picard.PoincareBundle.Ordinary.LineDescentUniqueness.existsUnique_iso f D hD
    (Picard.PoincareBundle.Line.Bundles.LineBundle.trivial Y) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm)
    (framedUnitRecovery_compatible f s t hk D e he)
  exact ⟨a ≪≫ b.symm⟩

end

/-! Keep the framed recovery equations at the level of actual
isomorphisms before taking their native module-morphism projections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

theorem iso_square_hom {C : Type*} [Category* C] {A B X Y : C}
    (a : A ≅ B) (b : B ≅ Y) (c : A ≅ X) (d : X ≅ Y) (h : a ≪≫ b = c ≪≫ d) :
    a.hom ≫ b.hom = c.hom ≫ d.hom := congrArg CategoryTheory.Iso.hom h

theorem ordinaryOverlap_frame_iso {X Y R : Scheme.{0}} (f : X ⟶ Y)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (q : R ⟶ Y) (s t : R ⟶ X) (hs : s ≫ f = q) (ht : t ≫ f = q)
    (he : D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) s t hs ht ≫
      ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t).hom =
        ((Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s).hom) :
    Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso f D q s t hs ht ≪≫
        ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t) =
      (Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s := by
  apply CategoryTheory.Iso.ext
  rw [Iso.trans_hom, Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso_hom]
  exact he

theorem framedUnitRecovery_compatible_iso {X Y R : Scheme.{0}} (f : X ⟶ Y) (s t : R ⟶ X)
    (hk : IsKernelPair f s t)
    (D : Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (e : D.obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (he : Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso f D (t ≫ f) s t hk.w rfl ≪≫
        ((Scheme.Modules.pullback t).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso t) =
      (Scheme.Modules.pullback s).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso s) :
    (Scheme.Modules.pullback (pullback.fst f f)).mapIso
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm) ≪≫
      Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D =
    (Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≪≫
        (Scheme.Modules.pullback (pullback.snd f f)).mapIso
          (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f ≪≫ e.symm) := by
  have h := congrArg CategoryTheory.Iso.hom he
  rw [Iso.trans_hom, Picard.PoincareBundle.Ordinary.OverlapPullback.overlapIso_hom] at h
  apply CategoryTheory.Iso.ext
  exact framedUnitRecovery_compatible f s t hk D e h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FramedLineRecovery
