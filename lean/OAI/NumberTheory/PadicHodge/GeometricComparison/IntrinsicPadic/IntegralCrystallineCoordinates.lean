import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineLimit
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimitProjection

/-! # Integral Crystalline Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineCoordinates.IntrinsicPadicIntegralCrystallineCoordinates

noncomputable section

/-! The completed original integral/crystalline comparison has exactly
the original finite principal-quotient comparison as each bounded restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.Coefficient.IntrinsicPadicSmallQuotientTotal.coefficients p
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.Integral.EtaleAffineCover.IntegralEtaleAffineCoverSections.opens ℤ_[p] X
local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntegralFirst.ThreeCechCompletion.IntegralFirstThreeCechCompletion.complex ℤ_[p] X U
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalTower.IntrinsicPadicPrincipalTower.targetDiagram p Y

theorem target_projection (n : ℕ) : (IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit.targetLimitIso p Y hprojective).hom ≫
    limit.π Q (op n) = ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction w n 1) := by
  have h := (CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates.limitIso p Y).inv_comp_eq.mpr
    (CrystallineTowerCoordinates.IntrinsicPadicCrystallineTowerCoordinates.limitIso_hom_π p Y n).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit.iso p Y hprojective).hom ≫ a) h).trans
      (CrystallineInverseLimitProjection.IntrinsicPadicCrystallineInverseLimitProjection.hom_π p Y hprojective n))

theorem comparison_projection (n : ℕ) : (IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit.iso p X Y f hp I hprojective).hom ≫
    ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallineCohomology.restriction w n 1) =
      (F).map (ModuleCat.ofHom (CochainQuotientCohomology.PrincipalCochainQuotient.reduction ℤ_[p] K (p : ℤ_[p]) (n + 1) 1)) ≫
        (PrincipalGlobalLevel.IntrinsicPadicPrincipalGlobalLevel.iso p X Y f hp I n).hom := by
  have h := (IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit.targetLimitIso p Y hprojective).inv_comp_eq.mpr
    (target_projection p Y hprojective n).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => (IntegralCrystallineLimit.IntrinsicPadicIntegralCrystallineLimit.sourceLimitIso p X Y f hp I).hom ≫ a) h).trans
      (IntegralTowerLimit.IntrinsicPadicIntegralTowerLimit.iso_π p X Y f hp I n))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralCrystallineCoordinates.IntrinsicPadicIntegralCrystallineCoordinates
