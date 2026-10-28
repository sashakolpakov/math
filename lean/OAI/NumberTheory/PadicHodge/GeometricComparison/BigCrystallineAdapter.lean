import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCohomologyAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Map

/-! # Big Crystalline Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BigCrystallineAdapter.CrystallineAdapter

noncomputable section

/-! The actual big-to-Cohomology crystalline comparison map, via the proved small-site adapter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k)))

abbrev W := WittVector p k
abbrev Coeff := ULift.{u + 1} (W p k)

abbrev BigIntegral (n : ℕ) := IntegralComparison.BigCrystallineCohomology.Cohomology
  (p := p) (J := Ideal.span {(p : W p k)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
  (IntegralComparison.Witt.Crystalline.wittStructureMap p k X) n

/-- Compose IntegralComparison's native restriction with exact transport to Cohomology's native small site. -/
def integralComparisonLarge (n : ℕ) : BigIntegral p k X n →ₗ[Coeff p k]
    AlgebraicGeometry.Crystalline.Cohomology.Site.integralCohomology p k X n :=
  (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.integralEquiv (p := p) (k := k) (X := X) n).toLinearMap.comp
    (IntegralComparison.Crystalline.Map.Comparison.integralComparison
      (p := p) (J := Ideal.span {(p : W p k)})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k)
      (IntegralComparison.Witt.Crystalline.wittStructureMap p k X) n)

def integralComparison (n : ℕ) : BigIntegral p k X n →ₗ[W p k]
    AlgebraicGeometry.Crystalline.Cohomology.Site.integralCohomology p k X n where
  toFun := integralComparisonLarge p k X n
  map_add' := (integralComparisonLarge p k X n).map_add
  map_smul' w x := by
    change integralComparisonLarge p k X n ((ULift.up w : Coeff p k) • x) =
      (ULift.up w : Coeff p k) • integralComparisonLarge p k X n x
    exact (integralComparisonLarge p k X n).map_smul _ _

def rationalComparison (n : ℕ) :
    TensorProduct (W p k) (FractionRing (W p k)) (BigIntegral p k X n) →ₗ[FractionRing (W p k)]
      AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n :=
  (integralComparison p k X n).baseChange (FractionRing (W p k))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BigCrystallineAdapter.CrystallineAdapter
