import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedFrobeniusGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTotal

/-! # Flasque Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FlasqueFrobenius.LevelZeroFlasqueFrobenius

noncomputable section

/-! The original flasque Cech/global comparison intertwines actual
level-zero Frobenius with the original bounded crystalline Ext pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y

def totalMap {ι : Type} (U : ι → Y.left.Opens) :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.totalMap.{1, 0, 2} R Y.left.carrier U (BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.flasqueMap p Y I)

theorem natural {ι : Type} (U : ι → Y.left.Opens) : Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U ≫
    totalMap p Y I U = BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal.map p Y I ≫
      Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.natural.{1, 0, 2} R Y.left.carrier U (BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.flasqueMap p Y I)

theorem homology {ι : Type} (U : ι → Y.left.Opens) (hU : iSup U = ⊤) (i : ℕ) :
    HomologicalComplex.homologyMap (totalMap p Y I U) i ≫
      (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso w 0 I U hU i).hom =
    (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso w 0 I U hU i).hom ≫
      ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg 0 i) := by
  let := Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.quasiIso w 0 I U hU
  have h := (HomologicalComplex.homologyMap_comp (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U)
    (totalMap p Y I U) i).symm.trans
      ((congrArg (fun a => HomologicalComplex.homologyMap a i) (natural p Y I U)).trans
        (HomologicalComplex.homologyMap_comp (BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal.map p Y I)
          (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U) i))
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (asIso (HomologicalComplex.homologyMap (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U) i))
    (asIso (HomologicalComplex.homologyMap (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w 0 I U) i))
    (HomologicalComplex.homologyMap (BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal.map p Y I) i)
    (HomologicalComplex.homologyMap (totalMap p Y I U) i) h.symm
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ (BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal.homology p Y I i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FlasqueFrobenius.LevelZeroFlasqueFrobenius
