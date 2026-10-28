import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveBicomplexLevelCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComponent

/-! # Integral Global Composite -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite

noncomputable section

/-! Compare the complete original integral-to-flasque composites
before H-one, with their source and target bicomplexes fixed explicitly. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y))) (n : ℕ)

local notation "Iq" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n I

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

def sourceBicomplex := (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).obj (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.source p X n)
def targetBicomplex := InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.target p X Y f I n

def levelBicomplex : sourceBicomplex p X n ⟶ targetBicomplex p X Y f I n :=
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n) ≫
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom

def finiteBicomplex : sourceBicomplex p X n ⟶ targetBicomplex p X Y f I n :=
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq) ≫
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom

theorem bicomponent (q r : ℕ) : ((levelBicomplex p X Y f hp I n).f q).f r =
    ((finiteBicomplex p X Y f hp I n).f q).f r := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    (InjectiveBicomplexLevelCoordinates.IntrinsicPadicInjectiveBicomplexLevelCoordinates.bicomponent p X Y f I n q r)
    ((((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq)).f q).f r x)

def levelMap := HomologicalComplex₂.total.map (levelBicomplex p X Y f hp I n) (.up ℕ)
def finiteMap := HomologicalComplex₂.total.map (finiteBicomplex p X Y f hp I n) (.up ℕ)

theorem homology : HomologicalComplex.homologyMap (levelMap p X Y f hp I n) 1 =
    HomologicalComplex.homologyMap (finiteMap p X Y f hp I n) 1 :=
  BicomplexComponent.BicomplexComponentHomology.homology (levelBicomplex p X Y f hp I n)
    (finiteBicomplex p X Y f hp I n) 1 (fun q r _ => bicomponent p X Y f hp I n q r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite
