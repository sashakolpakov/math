import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.ExtSectionNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.GlobalSectionRestriction

/-! # Open Section Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality

noncomputable section

/-! The actual frame de Rham section maps extend naturally to
the original Zariski open-section presheaf of every bounded frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)

local notation "C" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance constPreservesZero :
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def source : Cᵒᵖ ⥤ CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  SheafSectionNaturality.FrameSheafSectionNaturality.source f n ⋙
    (ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)

def globalTransformation : source (p := p) (J := J) (δ := δ) f n ⟶
    BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n ⋙
      (Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.globalSections f n).mapHomologicalComplex (.up ℕ) :=
  ExtSectionNaturality.FrameExtSectionNaturality.transformation f n ≫
    Functor.whiskerLeft (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n)
      (NatIso.mapHomologicalComplex (IntegralComparison.Ext.ZeroPresheafSections.iso.{u + 1, u, u + 1, u + 2}
        R (IntegralComparison.BoundedCrystalline.Site.topology (p := p) (J := J) (δ := δ) f n)) (.up ℕ)).hom

def openTransformation : source (p := p) (J := J) (δ := δ) f n ⋙
    (Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ) ⟶
      BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n ⋙
        (IntegralComparison.BoundedOpen.SectionComplex.functor f n).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (globalTransformation f n)
    ((Functor.const Y.Opensᵒᵖ : ModuleCat.{u + 2} R ⥤ Y.Opensᵒᵖ ⥤ ModuleCat.{u + 2} R).mapHomologicalComplex (.up ℕ)) ≫
      Functor.whiskerLeft (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n)
        (NatTrans.mapHomologicalComplex (Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation f n) (.up ℕ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality
