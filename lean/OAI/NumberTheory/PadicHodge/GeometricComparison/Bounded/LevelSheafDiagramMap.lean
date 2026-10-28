import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap

/-! # Level Sheaf Diagram Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafDiagramMap.BoundedLevelSheafDiagramMap

noncomputable section

/-! Natural maps of frame diagrams give natural augmented maps between
the original sheaf-resolution diagrams at two bounded levels. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) {C : Type v} [Category.{w} C]
  (Fn : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (Fm : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "TG" => Functor.mapHomologicalComplex T (ComplexShape.up ℕ)

variable (a : Fn ⋙ IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm ⟶ Fm)

def changeFrame := Functor.whiskerRight (NatTrans.op a) (BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f m ⋙ TG)

def changeLevel := Functor.whiskerLeft Fn.op (LevelSheafNaturality.BoundedLevelSheafNaturality.iso f n m hnm).hom

def transformation : Fm.op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f m ⋙ TG ⟶
    Fn.op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor f n :=
  changeFrame f n m hnm Fn Fm a ≫ changeLevel f n m hnm Fn

theorem app_eq (U : C) : (transformation f n m hnm Fn Fm a).app (op U) =
    IntegralComparison.BoundedLevel.FrameMap.map f n m hnm (a.app U) := rfl

theorem augmentation (U : C) :
    IntegralComparison.Single.ComplexTransport.map T (IntegralComparison.Bounded.CohomologyTransition.structureIso f n m hnm)
      (IntegralComparison.Bounded.RelativeSheafComplex.augmentation f m (Fm.obj U)) ≫
        (transformation f n m hnm Fn Fm a).app (op U) =
      IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n (Fn.obj U) :=
  IntegralComparison.BoundedLevel.FrameMap.augmentation f n m hnm (a.app U)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.LevelSheafDiagramMap.BoundedLevelSheafDiagramMap
