import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower
import OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.IntrinsicCechLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineTowerCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralTowerLimit

/-! # Integral Crystalline Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit

noncomputable section

/-! The completed integral coordinate Cech H-one compares with original
big crystalline H-one via their original quotient towers. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "C" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U

local instance padic_complete : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
  rw [← PadicInt.maximalIdeal_eq_span_p]
  infer_instance

def sourceLimitIso : (F).obj ((C).homology 1) ≅
    limit (PrincipalTower.IntrinsicPadicPrincipalTower.targetDiagram p Y) :=
  IntegralTowerLimit.IntrinsicPadicIntegralTowerLimit.iso p X Y f hp I

def targetLimitIso : ModuleCat.of R (IntegralComparison.BigCrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1) ≅
      limit (PrincipalTower.IntrinsicPadicPrincipalTower.targetDiagram p Y) :=
  CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit.iso p Y hprojective ≪≫
    (CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates.limitIso p Y).symm

def iso : (F).obj ((C).homology 1) ≅
    ModuleCat.of R (IntegralComparison.BigCrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1) :=
  sourceLimitIso p X Y f hp I ≪≫ (targetLimitIso p Y hprojective).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit
