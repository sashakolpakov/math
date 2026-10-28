import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PulledHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.RestrictionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.HomologyMapPostcomposition

/-! # Presheaf Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PresheafRestriction

noncomputable section

/-! Original crystalline frame comparisons commute on homology with actual presheaf restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
  (FY : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)]
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  (FX : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n FX)]
  (α : (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "IX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricResolution.resolution g hg n I

def restriction : Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2}
    R (BoundedCrystalline.Site.topology fY n) I.cocomplex ⟶ Bounded.GeometricResolution.complex g hg n I :=
  Sheaf.PresheafSectionRestriction.complexMap G R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n) I.cocomplex

omit [IsSeparated f] in
theorem global_eq : Presheaf.Comparison.map fY n FY I ≫ restriction g hg n I =
    PulledHomology.globalComparison g hg n FY I ≫
      (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom :=
  ConstantSection.RestrictionComposition.map.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology fY n)
    (DeRhamSections.frameComplex fY n FY)
    (DeRhamSections.sheafMap fY n FY) (Injective.Comparison.map fY n FY I)

omit [IsSeparated fY] [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)] in
theorem local_component (i : ℕ) : (PulledHomology.localComparison g hg n FY I FX α).f i ≫
    (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom.f i =
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map ((SectionChange.frameMap α).f i) ≫
        (Presheaf.Comparison.map f n FX IX).f i :=
  (Category.assoc _ _ _).trans
    (congrArg (fun a => (ModuleCat.uliftFunctor.{u + 2, u + 1} R).map
      ((SectionChange.frameMap α).f i) ≫ a)
        ((Category.assoc _ _ _).trans
          (Presheaf.Comparison.factorization_component f n FX IX i).symm))

omit [IsSeparated fY] [QuasiIso (Bounded.RelativeSheafComplex.augmentation fY n FY)] in
theorem local_eq : PulledHomology.localComparison g hg n FY I FX α ≫
    (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom =
      ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (SectionChange.frameMap α) ≫ Presheaf.Comparison.map f n FX IX := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact local_component g hg n FY I FX α i

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap
      (Presheaf.Comparison.map fY n FY I ≫ restriction g hg n I) i =
    HomologicalComplex.homologyMap
      (((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (.up ℕ)).map
        (SectionChange.frameMap α) ≫ Presheaf.Comparison.map f n FX IX) i :=
  (congrArg (fun a => HomologicalComplex.homologyMap a i) (global_eq g hg n FY I)).trans
    ((HomologyMapPostcomposition.equality
      (PulledHomology.globalComparison g hg n FY I)
      (PulledHomology.localComparison g hg n FY I FX α)
      (Sheaf.PresheafSectionComplex.complexIso R (BoundedCrystalline.Site.topology f n) (IX).cocomplex).hom i
      (PulledHomology.homology g hg n FY I FX α i)).trans
        (congrArg (fun a => HomologicalComplex.homologyMap a i) (local_eq g hg n FY I FX α)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.PresheafRestriction
