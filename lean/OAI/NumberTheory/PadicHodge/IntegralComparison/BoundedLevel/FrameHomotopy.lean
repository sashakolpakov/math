import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective

/-! # Frame Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomotopy

noncomputable section

/-! The actual frame comparisons commute with bounded-level restriction up to chain homotopy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) (Fm : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m Fm)]
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I
local notation "K" => Functor.obj (Functor.mapHomologicalComplex T (ComplexShape.up ℕ))
  (Bounded.RelativeSheafComplex.complex f m Fm)
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PulledAugmentation.augmentation f n m hnm Fm

def globalMap : K ⟶ (In).cocomplex :=
  ((T).mapHomologicalComplex (ComplexShape.up ℕ)).map (BoundedFrame.Injective.Comparison.map f m Fm Im)

theorem global_augmentation : a ≫ globalMap f n m hnm Fm I = (In).ι := by
  have h := (Single.ComplexTransportNaturality.comp T (Bounded.CohomologyTransition.structureIso f n m hnm)
    (Bounded.RelativeSheafComplex.augmentation f m Fm) (BoundedFrame.Injective.Comparison.map f m Fm Im)).trans
      (congrArg (Single.ComplexTransport.map T (Bounded.CohomologyTransition.structureIso f n m hnm))
        (BoundedFrame.Injective.Comparison.augmentation f m Fm Im))
  exact h.trans (Resolution.augmentation_eq f n m hnm I)

variable (Fn : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n Fn)]
  (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj Fn ⟶ Fm)

def localMap : K ⟶ (In).cocomplex := FrameMap.map f n m hnm α ≫
  BoundedFrame.Injective.Comparison.map f n Fn In

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m Fm)] in
theorem local_augmentation : a ≫ localMap f n m hnm Fm I Fn α = (In).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ BoundedFrame.Injective.Comparison.map f n Fn In)
      (FrameMap.augmentation f n m hnm α)).trans
        (BoundedFrame.Injective.Comparison.augmentation f n Fn In))

def homotopy : Homotopy (globalMap f n m hnm Fm I) (localMap f n m hnm Fm I Fn α) := by
  letI : QuasiIso a := Single.ComplexTransportNaturality.quasiIso T
    (Bounded.CohomologyTransition.structureIso f n m hnm) (Bounded.RelativeSheafComplex.augmentation f m Fm)
  exact Augmented.ResolutionHomotopy.homotopy K a In
    (globalMap f n m hnm Fm I) (localMap f n m hnm Fm I Fn α)
    ((global_augmentation f n m hnm Fm I).trans (local_augmentation f n m hnm Fm I Fn α).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomotopy
