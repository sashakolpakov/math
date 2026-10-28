import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FlasqueFrobenius

/-! # Frobenius Injective Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveGlobal.IntrinsicPadicFrobeniusInjectiveGlobal

noncomputable section

/-! The named native injective Cech comparison computes original global
bounded crystalline cohomology naturally under actual level-zero Frobenius. -/

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

abbrev totalIso := InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.totalIso p X Y f I 0

def totalMap : (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0).total (.up ℕ) ⟶ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I 0).total (.up ℕ) :=
  HomologicalComplex₂.total.map (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.nativeMap p X Y f I) (.up ℕ)

omit [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated] in
private theorem sectionsMap_coordinates :
    FrobeniusInjectiveSectionMap.IntrinsicPadicFrobeniusInjectiveSectionMap.map p X Y f I0 =
    FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.sectionsMap p X Y f I := rfl

private abbrev nativeMap_coordinates :=
  congrArg (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.cechFunctor p X).map
    (sectionsMap_coordinates p X Y f I)

abbrev totalMap_coordinates :=
  congrArg (fun a => HomologicalComplex₂.total.map a (.up ℕ))
    (nativeMap_coordinates p X Y f I)

theorem total_natural : totalMap p X Y f I ≫ (totalIso p X Y f I).hom =
    (totalIso p X Y f I).hom ≫ LevelZero.FlasqueFrobenius.LevelZeroFlasqueFrobenius.totalMap p Y I0 U := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{2} R) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.nativeMap p X Y f I)
    (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.comparisonIso p X Y f I).hom).symm.trans
      ((congrArg T.map (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.bicomplex_natural p X Y f I)).trans
        (T.map_comp (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.comparisonIso p X Y f I).hom (FrobeniusInjectiveCech.IntrinsicPadicFrobeniusInjectiveCech.targetMap p X Y f I)))

abbrev homologyIso (i : ℕ) := InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.homologyIso p X Y f I 0 i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (totalMap p X Y f I) i ≫
    (homologyIso p X Y f I i).hom =
    (homologyIso p X Y f I i).hom ≫ ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg 0 i) := by
  have h₁ := (HomologicalComplex.homologyMap_comp (totalMap p X Y f I) (totalIso p X Y f I).hom i).symm.trans
    ((congrArg (fun q => HomologicalComplex.homologyMap q i) (total_natural p X Y f I)).trans
      (HomologicalComplex.homologyMap_comp (totalIso p X Y f I).hom (LevelZero.FlasqueFrobenius.LevelZeroFlasqueFrobenius.totalMap p Y I0 U) i))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁
    (LevelZero.FlasqueFrobenius.LevelZeroFlasqueFrobenius.homology p Y I0 U (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusInjectiveGlobal.IntrinsicPadicFrobeniusInjectiveGlobal
