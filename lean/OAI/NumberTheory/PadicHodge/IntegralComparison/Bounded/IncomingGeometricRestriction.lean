import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingChartRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSection.RestrictionComposition
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ResolutionComposition

/-! # Incoming Geometric Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingGeometricRestriction

noncomputable section

/-! Incoming-subsite restriction agrees with the original geometric section restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) [Mono g] [Mono h]
  (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fZ n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "Rh" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) h hh n
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition.overBase g h hg hh

theorem component (i : ℕ) :
    (GeometricOpenSections.complexIso h hh n I).hom.f i ≫
      (Sheaf.PresheafSectionRestriction.map.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n)).app
        ((Rh).obj (I.cocomplex.X i)) ≫
          (Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R (BoundedCrystalline.Site.topology fX n)).map
            (RestrictionComposition.objectIso g h hg hh n (I.cocomplex.X i)).hom =
    (IncomingChartRestriction.map fZ g h n I).f i ≫
      (GeometricOpenSections.complexIso (g ≫ h) hc n I).hom.f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply NatTrans.ext
  funext U
  change x.down.app (op ((BoundedOpen.Equivalence.openFunctor h hh n).obj ((G).obj U.unop))) ≫
    (RestrictionComposition.objectIso g h hg hh n (I.cocomplex.X i)).hom.hom.app U = _
  exact (congrArg (fun a =>
    x.down.app (op ((BoundedOpen.Equivalence.openFunctor h hh n).obj ((G).obj U.unop))) ≫ a)
      (RestrictionComposition.component g h hg hh n (I.cocomplex.X i) U)).trans
        ((x.down.naturality (IncomingChartRestriction.comparison g h n hg hh U.unop).op).symm.trans
          (Category.id_comp _))

theorem complexes :
    (GeometricOpenSections.complexIso h hh n I).hom ≫
      Sheaf.PresheafSectionRestriction.complexMap.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n)
        (GeometricResolution.resolution h hh n I).cocomplex ≫
          ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
            (BoundedCrystalline.Site.topology fX n)).mapHomologicalComplex (.up ℕ)).map
              (ResolutionComposition.iso g h hg hh n I).hom =
    IncomingChartRestriction.map fZ g h n I ≫
      (GeometricOpenSections.complexIso (g ≫ h) hc n I).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component g h hg hh n I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingGeometricRestriction
