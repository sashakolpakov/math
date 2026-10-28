import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PresheafExt
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Open Section Level Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal

noncomputable section

/-! Restriction at the top open is the original global crystalline
cochain restriction and induces its original bounded Ext transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I

def map := ((IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex (.up ℕ)).map
  (OpenSectionLevel.BoundedOpenSectionLevel.complexMap f n m hnm I)

theorem coordinates : (IntegralComparison.BoundedOpen.SectionGlobal.complexIso f m Im).hom ≫ BoundedOpenSectionLevelGlobal.map f n m hnm I =
    IntegralComparison.BoundedLevel.FramePresheafRestriction.restriction f n m hnm I ≫
      (IntegralComparison.BoundedOpen.SectionGlobal.complexIso f n In).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (BoundedOpenSectionLevelGlobal.map f n m hnm I) i ≫
    (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso f n In i).hom =
      (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso f m Im i).hom ≫
        ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map f n m hnm i) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.homology
    (IntegralComparison.BoundedOpen.SectionGlobal.complexIso f m Im) (IntegralComparison.BoundedOpen.SectionGlobal.complexIso f n In)
    (IntegralComparison.BoundedLevel.FramePresheafRestriction.restriction f n m hnm I) (BoundedOpenSectionLevelGlobal.map f n m hnm I)
    (coordinates f n m hnm I).symm i
  have h₂ := IntegralComparison.BoundedLevel.PresheafExt.homology f n m hnm I i
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ h₂

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal
