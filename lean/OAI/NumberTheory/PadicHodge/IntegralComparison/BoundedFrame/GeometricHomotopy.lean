import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Injective
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution

/-! # Geometric Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricHomotopy

noncomputable section

/-!
# IntegralComparison: original frame-to-injective comparisons commute with chart restriction up to homotopy
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg n I
local notation "K" => CategoryTheory.Functor.obj
  (CategoryTheory.Functor.mapHomologicalComplex R (ComplexShape.up ℕ))
  (Bounded.RelativeSheafComplex.complex fY n FY)
local notation "aY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg n FY

def globalMap : K ⟶ (IX).cocomplex :=
  ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map (Injective.Comparison.map fY n FY I)

theorem global_augmentation : aY ≫ globalMap g hg n FY I = (IX).ι :=
  (Single.ComplexTransportNaturality.comp R (BoundedOpen.Sheaves.structureTransport g hg n)
    (Bounded.RelativeSheafComplex.augmentation fY n FY) (Injective.Comparison.map fY n FY I)).trans
      (congrArg (Single.ComplexTransport.map R (BoundedOpen.Sheaves.structureTransport g hg n))
        (Injective.Comparison.augmentation fY n FY I))

variable [IsSeparated f] (FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n FX)]
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

def localMap : K ⟶ (IX).cocomplex := GeometricMap.map g hg n α ≫
  Injective.Comparison.map f n FX IX

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)] in
theorem local_augmentation : aY ≫ localMap g hg n FY I FX α = (IX).ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ Injective.Comparison.map f n FX IX)
      (GeometricMap.augmentation g hg n α)).trans
        (Injective.Comparison.augmentation f n FX IX))

def homotopy : Homotopy (globalMap g hg n FY I) (localMap g hg n FY I FX α) := by
  letI : QuasiIso aY := Single.ComplexTransportNaturality.quasiIso R
    (BoundedOpen.Sheaves.structureTransport g hg n) (Bounded.RelativeSheafComplex.augmentation fY n FY)
  exact Augmented.ResolutionHomotopy.homotopy K aY IX (globalMap g hg n FY I) (localMap g hg n FY I FX α)
    ((global_augmentation g hg n FY I).trans (local_augmentation g hg n FY I FX α).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.GeometricHomotopy
