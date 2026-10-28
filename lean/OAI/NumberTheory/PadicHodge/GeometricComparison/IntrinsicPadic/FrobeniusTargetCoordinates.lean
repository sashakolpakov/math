import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComponent

/-! # Frobenius Target Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusTargetCoordinates.IntrinsicPadicFrobeniusTargetCoordinates

noncomputable section

/-! Frobenius coordinates on the named target complexes shared by the
original native integral comparison and injective Cech comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "I0" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap 0 I
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f

local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

/-- The original section map with the common native bicomplex endpoints. -/
private def nativeCoordinateMap : InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0 ⟶ InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0 :=
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map
    (FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f I0)

def cochainMap : IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I 0 ⟶
    IntegralCechLevel.IntrinsicPadicIntegralCechLevel.target p X Y f I 0 :=
  HomologicalComplex₂.total.map (nativeCoordinateMap p X Y f I) (.up ℕ)

def homologyMap : IntegralCechLevel.IntrinsicPadicIntegralCechLevel.targetHOne p X Y f I 0 ⟶
    IntegralCechLevel.IntrinsicPadicIntegralCechLevel.targetHOne p X Y f I 0 :=
  HomologicalComplex.homologyMap (cochainMap p X Y f I) 1

abbrev cochain_coordinates :=
  FrobeniusInjectiveGlobal.IntrinsicPadicFrobeniusInjectiveGlobal.totalMap_coordinates p X Y f I

private theorem component_coordinates (q r : ℕ) :
    ((nativeCoordinateMap p X Y f I).f q).f r =
    ((FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.nativeMap p X Y f I).f q).f r := rfl

theorem homology_coordinates : IntrinsicPadicFrobeniusTargetCoordinates.homologyMap p X Y f I =
    HomologicalComplex.homologyMap (FrobeniusInjectiveGlobal.IntrinsicPadicFrobeniusInjectiveGlobal.totalMap p X Y f I) 1 :=
  BicomplexComponent.BicomplexComponentHomology.homology
    (nativeCoordinateMap p X Y f I)
    (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.nativeMap p X Y f I) 1
    (fun q r _ => component_coordinates p X Y f I q r)

theorem natural : IntrinsicPadicFrobeniusTargetCoordinates.homologyMap p X Y f I ≫
    (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I 0 1).hom =
      (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I 0 1).hom ≫
        ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg 0 1) :=
  (congrArg (fun q => q ≫ (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I 0 1).hom)
    (homology_coordinates p X Y f I)).trans (FrobeniusInjectiveGlobal.IntrinsicPadicFrobeniusInjectiveGlobal.homology p X Y f I 1)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusTargetCoordinates.IntrinsicPadicFrobeniusTargetCoordinates
