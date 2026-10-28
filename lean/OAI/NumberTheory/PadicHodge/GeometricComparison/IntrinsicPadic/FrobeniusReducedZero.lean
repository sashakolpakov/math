import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusTargetCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusImage
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.ImageZero

/-! # Frobenius Reduced Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero

noncomputable section

/-! Actual bounded crystalline Frobenius kills the first Hodge image
under the original reduced native global comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "Iq" => fun q : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap q I
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.source p X 0
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "b" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f (Iq 0)

def inclusion :
    (((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).obj (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.brutal K 1)).total (.up ℕ)).homology 1 ⟶
      IntegralCechLevel.IntrinsicPadicIntegralCechLevel.sourceHOne p X 0 := HomologicalComplex.homologyMap
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1)) 1

def frobenius : End (ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap 0 1)) :=
  ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg 0 1)

abbrev target_natural :=
  FrobeniusTargetCoordinates.IntrinsicPadicFrobeniusTargetCoordinates.natural p X Y f I

private def injectiveMap :
    IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.target p X Y f I 0 ⟶
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.target p X Y f I 0 :=
  FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f (Iq 0)

private def frameFactor :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.map (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.transformation p X Y f hp 0) ≫
    FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation.map p X Y f hp

private def frameMap := FrameInjective.IntrinsicPadicFrameInjectiveComparison.map p X Y f hp 0 (Iq 0)

private def nativeHomotopy :=
  show Homotopy
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I 0 ≫ injectiveMap p X Y f I)
    (frameFactor p X Y f hp ≫ frameMap p X Y f hp I) from
      FrobeniusImage.IntrinsicPadicFrobeniusHodgeImage.homotopy p X Y f hp (Iq 0)

private theorem image_zero : inclusion p X ≫
    IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonHOne p X Y f hp I 0 ≫
      FrobeniusTargetCoordinates.IntrinsicPadicFrobeniusTargetCoordinates.homologyMap p X Y f I = 0 :=
  Cech.HomotopyImageZero.CechHomotopyImageZero.homology.{1, 2, 0, 0} R E (AlgebraicGeometry.Crystalline.Cohomology.HodgeFiltrationD.HodgeFiltration.inclusion K 1)
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I 0)
    (injectiveMap p X Y f I) (frameFactor p X Y f hp) (frameMap p X Y f hp I)
    (nativeHomotopy p X Y f hp I)
    (FrobeniusFrameTruncation.IntrinsicPadicFrobeniusFrameTruncation.integral_source_zero p X Y f hp)

theorem homology : inclusion p X ≫
    (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I 0).hom ≫ frobenius p Y = 0 := by
  rw [IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso_hom]
  exact ImageZero.ComparisonImageZero.transfer (inclusion p X)
    (IntegralCechLevel.IntrinsicPadicIntegralCechLevel.comparisonHOne p X Y f hp I 0)
    (FrobeniusTargetCoordinates.IntrinsicPadicFrobeniusTargetCoordinates.homologyMap p X Y f I)
    (InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I 0 1).hom (frobenius p Y)
    (image_zero p X Y f hp I)
    (target_natural p X Y f I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusReducedZero.IntrinsicPadicFrobeniusReducedHodgeZero
