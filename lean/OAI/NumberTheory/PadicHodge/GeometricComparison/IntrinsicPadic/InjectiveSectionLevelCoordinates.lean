import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionComplexRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechLevel

/-! # Injective Section Level Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates

noncomputable section

/-! The original identity-coordinate isomorphisms between native,
open, and underlying flasque injective sections respect level maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left) (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I

def sectionsMap : ((S m).mapHomologicalComplex (.up ℕ)).obj (Im).cocomplex ⟶
    ((S n).mapHomologicalComplex (.up ℕ)).obj (In).cocomplex :=
  ((SectionLevelMap.IntrinsicPadicSectionLevelMap.transformation p X Y f n m hnm).mapHomologicalComplex (.up ℕ)).app (Im).cocomplex

omit [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem source : sectionsMap p X Y f n m hnm I ≫
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n In).hom =
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f m Im).hom ≫
      ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
        (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f)).mapHomologicalComplex (.up ℕ)).map
          (Bounded.OpenSectionLevel.BoundedOpenSectionLevel.complexMap wittMap n m hnm I) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [IsSeparated Y.hom] in
theorem target : Bounded.OpenSectionLevel.BoundedOpenSectionLevel.complexMap wittMap n m hnm I ≫
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap n In).inv =
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap m Im).inv ≫
      FlasqueCechTotal.FlasqueCechGlobalNaturality.presheafMap.{1, 0, 2} R Y.left.carrier
        (Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel.complexMap wittMap n m hnm I) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveSectionLevelCoordinates.IntrinsicPadicInjectiveSectionLevelCoordinates
