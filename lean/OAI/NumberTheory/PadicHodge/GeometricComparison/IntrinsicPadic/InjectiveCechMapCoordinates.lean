import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData

/-! # Injective Cech Map Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechMapCoordinates.IntrinsicPadicInjectiveCechMapCoordinates

noncomputable section

/-! The original Cech-total functor and the named native injective
comparison use the same actual section-level map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p))))
  (f : Y.left ⟶ X.left) (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

theorem bicomplex : (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm) =
      InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I := rfl

theorem total : Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm) =
      InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel.totalMap p X Y f n m hnm I := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechMapCoordinates.IntrinsicPadicInjectiveCechMapCoordinates
