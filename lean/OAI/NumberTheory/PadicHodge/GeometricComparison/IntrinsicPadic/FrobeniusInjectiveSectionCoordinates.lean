import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionComplexRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedOpenFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTotal

/-! # Frobenius Injective Section Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionCoordinates.IntrinsicPadicFrobeniusInjectiveSectionCoordinates

noncomputable section

/-! The original identity-coordinate isomorphisms between native,
open, and underlying flasque injective sections respect actual level-zero Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "S" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f

def sectionsMap : ((S 0).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
    ((S 0).mapHomologicalComplex (.up ℕ)).obj I.cocomplex :=
  FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f I

omit [Smooth X.hom] [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem source : sectionsMap p X Y f I ≫
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f 0 I).hom =
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f 0 I).hom ≫
      ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} R)
        (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f)).mapHomologicalComplex (.up ℕ)).map
          (LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact (Category.comp_id _).trans (Category.id_comp _).symm

omit [IsSeparated Y.hom] in
theorem target : LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I ≫
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap 0 I).inv =
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso wittMap 0 I).inv ≫
      FlasqueCechTotal.FlasqueCechGlobalNaturality.presheafMap.{1, 0, 2} R Y.left.carrier
        (LevelZero.BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.flasqueMap p Y I) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact (Category.comp_id _).trans (Category.id_comp _).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionCoordinates.IntrinsicPadicFrobeniusInjectiveSectionCoordinates
