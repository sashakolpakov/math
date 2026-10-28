import OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineSheafAdapter
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExtAdapter
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Small Crystalline Cohomology Adapter -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter

noncomputable section

/-! Comparison of integral and rational cohomology on the equivalent small sites. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
  {X : Over (Spec (CommRingCat.of k))}

/-- Integral cohomology comparison induced by exact transport of the actual coefficient sheaves. -/
def integralEquiv (n : ℕ) : IntegralComparison.Witt.Crystalline.integralCohomology p k X n ≃ₗ[SmallCrystallineSheafAdapter.SmallCrystallineAdapter.Coeff (p := p) (k := k)]
    AlgebraicGeometry.Crystalline.Cohomology.Site.integralCohomology p k X n := by
  let E := SmallCrystallineSheafAdapter.SmallCrystallineAdapter.modulesEquivalence (p := p) (k := k) (X := X)
  let A := SmallCrystallineSheafAdapter.SmallCrystallineAdapter.constant65 (p := p) (k := k) (X := X)
  let B := SmallCrystallineSheafAdapter.SmallCrystallineAdapter.structure65 (p := p) (k := k) (X := X)
  exact (ExtAdapter.extEquiv (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.Coeff (p := p) (k := k)) E A B n).trans
      (IntegralComparison.Etale.Frobenius.extIsoCongr (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.Coeff (p := p) (k := k))
        (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.constantIso (p := p) (k := k) (X := X)) (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.structureIso (p := p) (k := k) (X := X)) n)

def integralWittEquiv (n : ℕ) : IntegralComparison.Witt.Crystalline.integralCohomology p k X n ≃ₗ[SmallCrystallineSheafAdapter.SmallCrystallineAdapter.W (p := p) (k := k)]
    AlgebraicGeometry.Crystalline.Cohomology.Site.integralCohomology p k X n where
  toFun := integralEquiv (p := p) (k := k) (X := X) n
  invFun := (integralEquiv (p := p) (k := k) (X := X) n).symm
  left_inv := (integralEquiv (p := p) (k := k) (X := X) n).left_inv
  right_inv := (integralEquiv (p := p) (k := k) (X := X) n).right_inv
  map_add' := (integralEquiv (p := p) (k := k) (X := X) n).map_add
  map_smul' w x := by
    change integralEquiv (p := p) (k := k) (X := X) n ((ULift.up w : SmallCrystallineSheafAdapter.SmallCrystallineAdapter.Coeff (p := p) (k := k)) • x) =
      (ULift.up w : SmallCrystallineSheafAdapter.SmallCrystallineAdapter.Coeff (p := p) (k := k)) • integralEquiv (p := p) (k := k) (X := X) n x
    exact (integralEquiv (p := p) (k := k) (X := X) n).map_smul _ _

/-- Rationalization preserves the independently constructed small-site cohomology equivalence. -/
def rationalEquiv (n : ℕ) : IntegralComparison.Witt.Crystalline.rationalCohomology p k X n ≃ₗ[FractionRing (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.W (p := p) (k := k))]
    AlgebraicGeometry.Crystalline.Cohomology.Site.rationalCohomology p k X n :=
  (integralWittEquiv (p := p) (k := k) (X := X) n).baseChange
    (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.W (p := p) (k := k)) (FractionRing (SmallCrystallineSheafAdapter.SmallCrystallineAdapter.W (p := p) (k := k))) _ _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SmallCrystallineCohomologyAdapter.SmallCrystallineAdapter
