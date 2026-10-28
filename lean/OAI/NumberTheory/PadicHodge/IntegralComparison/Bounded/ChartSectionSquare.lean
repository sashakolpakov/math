import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IncomingGeometricRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartEvaluationRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricSectionsCongr
import OAI.NumberTheory.PadicHodge.IntegralComparison.IsoSectionSquare

/-! # Chart Section Square -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartSectionSquare

noncomputable section

/-! The original geometric and Zariski restrictions commute after identifying nested chart resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y Z : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)}
  {fY : Y ⟶ Spec (CommRingCat.of B)} {fZ : Z ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (h : Y ⟶ Z) (j : X ⟶ Z)
  [IsOpenImmersion g] [IsOpenImmersion h] [IsOpenImmersion j]
  (hg : g ≫ fY = fX) (hh : h ≫ fZ = fY) (hj : j ≫ fZ = fX) (e : g ≫ h = j) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fZ n))
  {U V : Z.Opens} (hVU : V ≤ U) (eU : h.opensRange = U) (eV : j.opensRange = V)

include e eV in
theorem composite_range : (g ≫ h).opensRange = V := by
  have hr : (g ≫ h).opensRange = j.opensRange := by
    apply SetLike.coe_injective
    exact congrArg (fun t : X ⟶ Z => Set.range t) e
  exact hr.trans eV

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "hc" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.PostcomposeComposition.overBase g h hg hh
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "eC" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartSectionSquare.composite_range g h j e eV

theorem square :
    ((GeometricOpenSections.complexIso h hh n I).inv ≫
      (ChartEvaluationCoordinates.iso fZ h n U eU I).hom) ≫
        ChartEvaluationRestriction.map fZ n I hVU =
    Sheaf.PresheafSectionRestriction.complexMap.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology fX n) (BoundedCrystalline.Site.topology fY n)
      (GeometricResolution.resolution h hh n I).cocomplex ≫
        ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
          (BoundedCrystalline.Site.topology fX n)).mapHomologicalComplex (.up ℕ)).map
            (ResolutionComposition.iso g h hg hh n I).hom ≫
        ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2} R
          (BoundedCrystalline.Site.topology fX n)).mapHomologicalComplex (.up ℕ)).map
            (ResolutionCongr.iso (g ≫ h) j hc hj e n I).hom ≫
          (GeometricOpenSections.complexIso j hj n I).inv ≫
            (ChartEvaluationCoordinates.iso fZ j n V eV I).hom :=
  IsoSectionSquare.square
    (GeometricOpenSections.complexIso h hh n I)
    (GeometricOpenSections.complexIso (g ≫ h) hc n I)
    (GeometricOpenSections.complexIso j hj n I)
    (GeometricSectionsCongr.openIso (g ≫ h) j e n I).hom
    (IncomingChartRestriction.map fZ g h n I) _ _ _
    (ChartEvaluationCoordinates.iso fZ h n U eU I).hom
    (ChartEvaluationCoordinates.iso fZ j n V eV I).hom
    (ChartEvaluationCoordinates.iso fZ (g ≫ h) n V eC I).hom
    (ChartEvaluationRestriction.map fZ n I hVU)
    (IncomingGeometricRestriction.complexes g h hg hh n I)
    (GeometricSectionsCongr.complexes (g ≫ h) j hc hj e n I)
    (ChartEvaluationRestriction.complexes fZ n I hVU g h eU eC)
    (GeometricSectionsCongr.evaluation (g ≫ h) j e n I V eC eV)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.ChartSectionSquare
