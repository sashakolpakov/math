import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.RestrictionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPostcomposition

/-! # Frame Presheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePresheafRestriction

noncomputable section

/-! Original crystalline frame comparisons commute on homology with actual presheaf restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) (FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)]
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))
  (FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n FX)]
  (α : (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I

def restriction : Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2}
    R (BoundedCrystalline.Site.topology f m) (BoundedCrystalline.CrystallineCohomology.resolution f m I).cocomplex ⟶ Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology f n) (IX).cocomplex :=
  Sheaf.PresheafSectionRestriction.complexMap G R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m) (BoundedCrystalline.CrystallineCohomology.resolution f m I).cocomplex

theorem global_eq : BoundedFrame.Presheaf.Comparison.map f m FY (BoundedCrystalline.CrystallineCohomology.resolution f m I) ≫ restriction f n m hnm I =
    FrameHomology.globalComparison f n m hnm FY I ≫
      (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom :=
  ConstantSection.RestrictionComposition.map.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)
    (BoundedFrame.DeRhamSections.frameComplex f m FY)
    (BoundedFrame.DeRhamSections.sheafMap f m FY) (BoundedFrame.Injective.Comparison.map f m FY (BoundedCrystalline.CrystallineCohomology.resolution f m I))

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)] in
theorem local_component (i : ℕ) : (FrameHomology.localComparison f n m hnm FY I FX α).f i ≫
    (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom.f i =
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((BoundedFrame.SectionChange.frameMap α).f i) ≫
        (BoundedFrame.Presheaf.Comparison.map f n FX IX).f i :=
  (Category.assoc _ _ _).trans
    (congrArg (fun a => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map
      ((BoundedFrame.SectionChange.frameMap α).f i) ≫ a)
        ((Category.assoc _ _ _).trans
          (BoundedFrame.Presheaf.Comparison.factorization_component f n FX IX i).symm))

omit [QuasiIso (Bounded.RelativeSheafComplex.augmentation f m FY)] in
theorem local_eq : FrameHomology.localComparison f n m hnm FY I FX α ≫
    (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom =
      ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.Presheaf.Comparison.map f n FX IX := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact local_component f n m hnm FY I FX α i

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (BoundedFrame.Presheaf.Comparison.map f m FY (BoundedCrystalline.CrystallineCohomology.resolution f m I) ≫ restriction f n m hnm I) i =
    HomologicalComplex.homologyMap
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.SectionChange.frameMap α) ≫ BoundedFrame.Presheaf.Comparison.map f n FX IX) i :=
  (congrArg (fun a => HomologicalComplex.homologyMap a i) (global_eq f n m hnm FY I)).trans
    ((HomologyMapPostcomposition.equality
      (FrameHomology.globalComparison f n m hnm FY I)
      (FrameHomology.localComparison f n m hnm FY I FX α)
      (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom i
      (FrameHomology.homology f n m hnm FY I FX α i)).trans
        (congrArg (fun a => HomologicalComplex.homologyMap a i) (local_eq f n m hnm FY I FX α)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePresheafRestriction
