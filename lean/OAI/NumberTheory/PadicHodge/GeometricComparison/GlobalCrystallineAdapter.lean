import OAI.NumberTheory.PadicHodge.GeometricComparison.BigCrystallineAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Global Crystalline Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalCrystallineAdapter.CrystallineAdapter

noncomputable section

/-! The native big-to-Cohomology crystalline comparison is an isomorphism for separated schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsSeparated X.hom]

theorem integralComparison_bijective (n : ℕ) : Function.Bijective
    (BigCrystallineAdapter.CrystallineAdapter.integralComparison p k X n) :=
  (SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter.integralEquiv (p := p) (k := k) (X := X) n).bijective.comp
    (IntegralComparison.Global.Crystalline.Comparison.comparison_bijective p k X n)

/-- The inverse comes from proved bijectivity of the actual restriction and sheaf-transport map. -/
def integralEquiv (n : ℕ) : BigCrystallineAdapter.CrystallineAdapter.BigIntegral p k X n ≃ₗ[BigCrystallineAdapter.CrystallineAdapter.W p k]
    AlgebraicGeometry.Crystalline.Cohomology.Site.integralCohomology p k X n :=
  LinearEquiv.ofBijective (BigCrystallineAdapter.CrystallineAdapter.integralComparison p k X n)
    (integralComparison_bijective p k X n)

def rationalEquiv (n : ℕ) :
    TensorProduct (BigCrystallineAdapter.CrystallineAdapter.W p k) (FractionRing (BigCrystallineAdapter.CrystallineAdapter.W p k)) (BigCrystallineAdapter.CrystallineAdapter.BigIntegral p k X n) ≃ₗ[FractionRing (BigCrystallineAdapter.CrystallineAdapter.W p k)]
      AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n :=
  (integralEquiv p k X n).baseChange (BigCrystallineAdapter.CrystallineAdapter.W p k) (FractionRing (BigCrystallineAdapter.CrystallineAdapter.W p k)) _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.GlobalCrystallineAdapter.CrystallineAdapter
