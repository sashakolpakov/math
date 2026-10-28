import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameSheafResolution
import OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicAugmentation
import OAI.AlgebraicGeometry.Crystalline.Cohomology.CrystallineFrame.SheafResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Small.CrystallineContinuous

/-! # Intrinsic Sheaf Transport -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport

noncomputable section

/-! # Exact sheaf transport of the original big crystalline frame resolution -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable (p : ℕ) [Fact p.Prime] (k B : Type u) [Field k] [CharP k p]
  [CommRing B] [Algebra k B]

local notation "W" => WittVector p k
local notation "R" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.CoefficientRing p k
local notation "X" => OAI.AlgebraicGeometry.Crystalline.Cohomology.AffineFrameCover.CrystallineAffineFrameCover.affineScheme k B
local notation "I" => Ideal.span {(p : W)}
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "bX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.Object p k X
local notation "Big" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.FrameLifts.BigCrystallineFrameLifts.Site p W B I γ bX
local notation "ι" => OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicLifts.BigCrystallineIntrinsicLifts.inclusion p k B
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Site.topology p k X
local notation "U" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.Object.topology (p := p) (B := W)
  (J := I) (δ := γ) (f := bX)
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Site.AffineThickening.topology
  (p := p) (B := W) (J := I) (δB := γ) (f := bX)

instance inclusion_continuous : (ι).IsContinuous T U :=
  Functor.isContinuous_comp NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.fromSmall T S U

instance inclusion_cocontinuous : (ι).IsCocontinuous T U :=
  isCocontinuous_comp NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineDpow.SmallCrystallineAdapter.to65
    NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.fromSmall T S

def restriction : Sheaf U (ModuleCat.{u + 1} R) ⥤ Sheaf T (ModuleCat.{u + 1} R) :=
  (ι).sheafPushforwardContinuous (ModuleCat.{u + 1} R) T U

instance restriction_additive : (restriction p k B).Additive where
  map_add := by intros; rfl

instance restriction_linear : (restriction p k B).Linear R where
  map_smul := by intros; rfl

instance restriction_leftAdjoint : (restriction p k B).IsLeftAdjoint :=
  ((ι).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} R) T U).isLeftAdjoint

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (restriction p k B) := by
  unfold restriction
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction p k B) := by
  infer_instance

def comparisonIso :
    FrameSheafResolution.BigCrystallineFrameSheafResolution.toSheaf p W B I γ bX ⋙ restriction p k B ≅
      IntrinsicResolution.BigCrystallineIntrinsicResolution.restriction p k B ⋙ PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X :=
  NatIso.ofComponents (fun P =>
    ((ι).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) T U).symm.app
      (P ⋙ FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W)) (by
    intro P Q f
    exact ((ι).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) T U).inv.naturality
      (Functor.whiskerRight f (FrameSheafResolution.BigCrystallineFrameSheafResolution.coefficientLift W)))

def structureIso : (restriction p k B).obj
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := I) (δ := γ) bX) ≅
      Site.structureSheaf p k X :=
  (comparisonIso p k B).app
      (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.modulePresheaf (p := p) (J := I) (δ := γ) bX) ≪≫
    (PolynomialSheafResolution.CrystallinePolynomialSheafResolution.toSheaf p k X).mapIso (IntrinsicAugmentation.BigCrystallineIntrinsicAugmentation.sourceIso p k B)

def constantIso : (restriction p k B).obj
    (NumberTheory.PadicHodge.IntegralComparison.BigCrystallineCohomology.constantUnit (p := p) (J := I) (δ := γ) bX) ≅
      Site.coefficientSheaf p k X :=
  ((ι).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} R) T U).symm.app
    ((Functor.const Bigᵒᵖ).obj (ModuleCat.of R R))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.BigCrystalline.IntrinsicSheafTransport.BigCrystallineIntrinsicSheafTransport
