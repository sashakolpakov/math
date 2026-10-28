import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalComposite
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.CompositeFactor

/-! # Integral Level Composite Factor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor

noncomputable section

/-! Factor the original level comparison through its checked full
integral-to-flasque composite. -/

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def finalMap := (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso w n Iq
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) 1).hom

theorem level : (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n).hom =
    HomologicalComplex.homologyMap
      (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.levelMap p X Y f hp I n) 1 ≫ finalMap p X Y f I n :=
  Functor.CompositeFactor.FunctorCompositeFactor.factor
    (HomologicalComplex₂.totalFunctor (ModuleCat.{2} R) (.up ℕ) (.up ℕ) (.up ℕ))
    (HomologicalComplex.homologyFunctor (ModuleCat.{2} R) (.up ℕ) 1)
    ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map
      (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n))
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom
    (finalMap p X Y f I n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor
