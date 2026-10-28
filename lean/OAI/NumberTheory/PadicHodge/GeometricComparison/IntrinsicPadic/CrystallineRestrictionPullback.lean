import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallinePullbackCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.PullbackRestriction

/-! # Crystalline Restriction Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback

noncomputable section

/-! Original big-to-bounded crystalline restriction commutes with
actual geometric pullback after descending to p-adic scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p)))) (g : Y ⟶ Y)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

theorem over_witt : g.left ≫ w = w := by
  simp only [IntegralComparison.Witt.Crystalline.wittStructureMap, ← Category.assoc, Over.w]

def pullback (n : ℕ) : CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.bounded p Y n →ₗ[ℤ_[p]]
    CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.bounded p Y n :=
  ((Coefficient.IntrinsicPadicCoefficientDescent.restrict p).map (ModuleCat.ofHom
    (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g.left (over_witt p Y g) n 1))).hom

theorem natural (n : ℕ) : (pullback p Y g n).comp (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y n) =
    (CrystallineRestrictionExt.IntrinsicPadicIntegralCrystallineReduction.restriction p Y n).comp (CrystallinePullbackCoordinates.IntrinsicPadicCrystallinePullbackCoordinates.integral p g) := by
  apply LinearMap.ext
  intro x
  exact IntegralComparison.BoundedCrystalline.PullbackRestriction.naturality g.left (over_witt p Y g) n 1 x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CrystallineRestrictionPullback.IntrinsicPadicCrystallineRestrictionPullback
