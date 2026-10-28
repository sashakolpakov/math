import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PullbackCoherence
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent
import OAI.AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames

/-! # Descent Kernel Pair Compatibility -/

namespace OAI.RepresentationTheory.Theta.Geometric.DescentKernelPairCompatibility

noncomputable section

/-! Compatibility on the actual scheme kernel pair implies compatibility
on every test scheme. The effective recovery is therefore an isomorphism
of the full ordinary descent data. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization
universe u

theorem nativePullback_map {X T U : Scheme.{u}} {M N : X.Modules}
    (b : M ⟶ N) (x : T ⟶ X) (r : U ⟶ T) (x' : U ⟶ X) (hx : r ≫ x = x') :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback ((Scheme.Modules.pullback x).map b) r x' x' hx hx =
      (Scheme.Modules.pullback x').map b := by
  let c := Scheme.Modules.pullbackComp r x ≪≫ Scheme.Modules.pullbackCongr hx
  change (c.app M).inv ≫ (Scheme.Modules.pullback r).map ((Scheme.Modules.pullback x).map b) ≫
    (c.app N).hom = _
  change c.inv.app M ≫ (Scheme.Modules.pullback x ⋙ Scheme.Modules.pullback r).map b ≫
    c.hom.app N = _
  rw [c.hom.naturality]
  simp only [Iso.inv_hom_id_app_assoc]

theorem descentHom_compatible_of_kernelPair {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D E : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (b : D.obj PUnit.unit ⟶ E.obj PUnit.unit)
    (hb : (Scheme.Modules.pullback (pullback.fst f f)).map b ≫
        E.hom (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
      D.hom (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f) pullback.condition rfl ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map b)
    {T : Scheme.{u}} (q : T ⟶ Y) (x y : T ⟶ X) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (Scheme.Modules.pullback x).map b ≫ E.hom q x y hx hy =
      D.hom q x y hx hy ≫ (Scheme.Modules.pullback y).map b := by
  let r := pullback.lift x y (hx.trans hy.symm)
  have hrx : r ≫ pullback.fst f f = x := pullback.lift_fst _ _ _
  have hry : r ≫ pullback.snd f f = y := pullback.lift_snd _ _ _
  have hrq : r ≫ (pullback.snd f f ≫ f) = q := by rw [← Category.assoc, hry, hy]
  have H := congrArg (fun a => AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback a r x y hrx hry) hb
  rw [Intrinsic.PullbackCoherence.nativePullback_comp _ _ r x x y hrx hrx hry,
    Intrinsic.PullbackCoherence.nativePullback_comp _ _ r x y y hrx hry hry,
    nativePullback_map, nativePullback_map,
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.hom_pullback E r _ q hrq _ _ _ _ x y hrx hry,
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.hom_pullback D r _ q hrq _ _ _ _ x y hrx hry] at H
  exact H

def descentKernelPairIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D E : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (b : D.obj PUnit.unit ≅ E.obj PUnit.unit)
    (hb : (Scheme.Modules.pullback (pullback.fst f f)).map b.hom ≫
        E.hom (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
      D.hom (pullback.snd f f ≫ f) (pullback.fst f f) (pullback.snd f f) pullback.condition rfl ≫
        (Scheme.Modules.pullback (pullback.snd f f)).map b.hom) : D ≅ E := by
  refine Pseudofunctor.DescentData.isoMk (fun _ => b) ?_
  intro T q a c x y hx hy
  cases a
  cases c
  exact descentHom_compatible_of_kernelPair f D E b.hom hb q x y hx hy

theorem canonicalDatum_relationGluing {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) :
    ((AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj N).hom
      (pullback.snd f f ≫ f) (i₁ := PUnit.unit) (i₂ := PUnit.unit)
      (pullback.fst f f) (pullback.snd f f) pullback.condition rfl =
    (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
      pullback.condition).hom.app N := by
  change (AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent f N).hom (pullback.snd f f ≫ f)
    (pullback.fst f f) (pullback.snd f f) pullback.condition rfl = _
  rw [AlgebraicGeometry.Picard.Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent_hom]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.trans_refl]
  rfl

def lineRecoveryDataIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (D : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f)) (N : Y.Modules)
    (b : (Scheme.Modules.pullback f).obj N ≅ D.obj PUnit.unit)
    (hb : (Scheme.Modules.pullback (pullback.fst f f)).map b.hom ≫
        (AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant.relationGluing f D).hom =
      (AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f)
        pullback.condition).hom.app N ≫ (Scheme.Modules.pullback (pullback.snd f f)).map b.hom) :
    (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj N ≅ D :=
  descentKernelPairIso f ((AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj N) D b
    (hb.trans (congrArg (fun a => a ≫ (Scheme.Modules.pullback (pullback.snd f f)).map b.hom)
      (canonicalDatum_relationGluing f N).symm))

def descendedLineDataIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] [IsLocallyNoetherian Y] [Flat f] [Surjective f]
    (D : AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => f))
    (hD : AlgebraicGeometry.Picard.PoincareBundle.Line.Bundles.IsLine (D.obj PUnit.unit)) :
    (AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization.modulePullbacks.toDescentData (fun (_ : PUnit.{1}) => f)).obj
      (AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLine f D hD).sheaf ≅ D :=
  lineRecoveryDataIso f D _ (AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso f D hD)
    (AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent.descendedLinePullbackIso_compatible f D hD)

end

end OAI.RepresentationTheory.Theta.Geometric.DescentKernelPairCompatibility
