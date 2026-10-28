import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineInverseLimit

/-! # Crystalline Inverse Limit -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit

noncomputable section

/-! Original big crystalline H-one is the original bounded Ext inverse
limit for the smooth proper projective prime-field fiber. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsProper Y.hom] [Smooth Y.hom]
  (hprojective : IntegralComparison.Projectivity.Construction.ProjectiveOver (ZMod p) Y.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def iso : ModuleCat.of R (IntegralComparison.BigCrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1) ≅
      limit (IntegralComparison.Crystalline.FiniteInverseLimit.diagram (p := p)
        (J := Ideal.span {(p : WittVector p (ZMod p))})
        (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 1) := by
  let := IntegralComparison.SmoothProper.CrystallineInverseLimit.inclusion_mono p (ZMod p) Y hprojective 1
  exact (IntegralComparison.Crystalline.FiniteInverseLimit.linearEquiv w 1).toModuleIso

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineInverseLimit.IntrinsicPadicCrystallineInverseLimit
