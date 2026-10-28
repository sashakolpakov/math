import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjectiveLevelHomotopy
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCoefficientLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveLevelMapCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TotalHomotopySquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralPresheafLevelData

/-! # Integral Cech Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel

noncomputable section

/-! The canonical integral quotient-to-injective comparison commutes
with original level restriction on Cech total H-one. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap m I
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

def source (q : ℕ) : CochainComplex (ModuleCat.{2} R) ℕ :=
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).obj
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.source p X q)).total (.up ℕ)

def target (q : ℕ) : CochainComplex (ModuleCat.{2} R) ℕ :=
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).obj
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.target p X Y f I q)).total (.up ℕ)

def sourceMap : source p X m ⟶ source p X n :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm)

def comparisonMap (q : ℕ) : source p X q ⟶ target p X Y f I q :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I q)

def targetMap : target p X Y f I m ⟶ target p X Y f I n :=
  Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)

def sourceHOne (q : ℕ) : ModuleCat.{2} R := (source p X q).homology 1

def targetHOne (q : ℕ) : ModuleCat.{2} R :=
  (target p X Y f I q).homology 1

def comparisonHOne (q : ℕ) : sourceHOne p X q ⟶ targetHOne p X Y f I q :=
  HomologicalComplex.homologyMap (comparisonMap p X Y f hp I q) 1

def sourceHOneMap : sourceHOne p X m ⟶ sourceHOne p X n :=
  HomologicalComplex.homologyMap (sourceMap p X n m hnm) 1

def targetHOneMap : targetHOne p X Y f I m ⟶ targetHOne p X Y f I n :=
  HomologicalComplex.homologyMap (targetMap p X Y f n m hnm I) 1

def homotopy : Homotopy
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m ≫
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm ≫
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n) :=
  IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.homotopy p X Y f hp I n m hnm

theorem total_left : Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m ≫
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm) =
    comparisonMap p X Y f hp I m ≫ targetMap p X Y f n m hnm I :=
  Cech.TotalHomotopySquare.CechTotalHomotopySquare.map_comp.{1, 2, 0, 0} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m)
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)

theorem total_right : Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm ≫
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n) =
    sourceMap p X n m hnm ≫ comparisonMap p X Y f hp I n :=
  Cech.TotalHomotopySquare.CechTotalHomotopySquare.map_comp.{1, 2, 0, 0} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm)
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n)

theorem homology_raw : HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
    (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I m ≫
      IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.targetMap p X Y f I n m hnm)) 1 =
    HomologicalComplex.homologyMap (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} R E
      (IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.sourceMap p X n m hnm ≫
        IntegralPresheafLevelData.IntrinsicPadicIntegralPresheafLevelData.comparison p X Y f hp I n)) 1 :=
  Cech.TotalHomotopyOne.CechTotalHomotopyHOne.homology.{1, 2, 0, 0} R E (homotopy p X Y f hp n m hnm I)

theorem homology : comparisonHOne p X Y f hp I m ≫ targetHOneMap p X Y f n m hnm I =
      sourceHOneMap p X n m hnm ≫ comparisonHOne p X Y f hp I n := by
  let H := fun (q : source p X m ⟶ target p X Y f I n) =>
    HomologicalComplex.homologyMap q 1
  have h := (congrArg H (total_left p X Y f hp n m hnm I).symm).trans
    ((homology_raw p X Y f hp n m hnm I).trans (congrArg H (total_right p X Y f hp n m hnm I)))
  exact (HomologicalComplex.homologyMap_comp (comparisonMap p X Y f hp I m) (targetMap p X Y f n m hnm I) 1).symm.trans
    (h.trans (HomologicalComplex.homologyMap_comp (sourceMap p X n m hnm) (comparisonMap p X Y f hp I n) 1))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCechLevel.IntrinsicPadicIntegralCechLevel
