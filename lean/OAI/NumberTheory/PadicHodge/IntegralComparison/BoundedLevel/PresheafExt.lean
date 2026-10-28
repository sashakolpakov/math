import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Ext
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.ExtRestrictionCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePresheafRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.SectionCohomologyCoordinates

/-! # Presheaf Ext -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PresheafExt

noncomputable section

/-! Actual bounded-level presheaf restriction induces exactly the original crystalline Ext transition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I
local notation "r" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FramePresheafRestriction.restriction f n m hnm I
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Ext.Comparison.complexMap f n m hnm I
local notation "en" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f n) (InjectiveResolution.cocomplex In)
local notation "em" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex.complexIso R (OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.topology f m) (InjectiveResolution.cocomplex Im)

theorem complexes : s ≫ (en).hom = (em).hom ≫ r :=
  Sheaf.ExtRestrictionCoordinates.complexes.{u + 1, u, u + 2} G R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m) (Im).cocomplex

theorem homology (i : ℕ) : HomologicalComplex.homologyMap r i ≫
    (Sheaf.PresheafSectionComplex.homologyIso R (BoundedCrystalline.Site.topology f n) In i).hom =
      (Sheaf.PresheafSectionComplex.homologyIso R (BoundedCrystalline.Site.topology f m) Im i).hom ≫
        ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i) :=
  Sheaf.SectionCohomologyCoordinates.homology.{u + 1, u, u + 2} R (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)
    In Im s r i (ModuleCat.ofHom (Bounded.CohomologyTransition.map f n m hnm i))
    (complexes f n m hnm I) (Ext.Comparison.homology f n m hnm I i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.PresheafExt
