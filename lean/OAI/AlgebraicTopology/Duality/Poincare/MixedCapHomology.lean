import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
import OAI.AlgebraicTopology.Products.CapCompatibility

/-! # Mixed Cap Homology -/

namespace OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

noncomputable section

/-!
# Actual scalar cohomology capped with integral homology

The pairing is the existing cap product after the proved coefficient map
on integral homology. Its representative formula is the finite mixed cap.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CapCompatibility

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]

/-- The finite mixed cap product restricted to actual cycles. -/
def mixedSingularCapCycles (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (p + q)) :
    Cohomology.Singular.ChainRepresentatives.chainCycles (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) q :=
  Products.CapBoundary.capCycles (TopCat.toSSet.obj X) p q c (IntegralHomologyCoefficients.integralToScalarSingularCycles X (p + q) z)

@[simp]
theorem mixedSingularCapCycles_val (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (p + q)) :
    (mixedSingularCapCycles X p q c z).val = IntegralCapCoefficients.mixedSingularCap X p q c.val z.val := rfl

/-- Cap scalar cohomology with integral homology using the actual coefficient
map, retaining the scalar output homology group. -/
def mixedSingularCapHomology (X : TopCat.{0}) (p q : ℕ) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p →ₗ[R]
      ((AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q) →ₗ[ℤ]
        (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X).homology q) where
  toFun c := ((Products.CapBoundary.singularCapHomology X p q c).restrictScalars ℤ).comp
    (IntegralHomologyCoefficients.integralToScalarSingularHomology X (p + q))
  map_add' c d := by
    apply LinearMap.ext
    intro z
    change Products.CapBoundary.singularCapHomology X p q (c + d) (IntegralHomologyCoefficients.integralToScalarSingularHomology X (p + q) z) = _
    rw [map_add, LinearMap.add_apply]
    rfl
  map_smul' r c := by
    apply LinearMap.ext
    intro z
    change Products.CapBoundary.singularCapHomology X p q (r • c) (IntegralHomologyCoefficients.integralToScalarSingularHomology X (p + q) z) = _
    rw [map_smul, LinearMap.smul_apply]
    rfl

@[simp]
theorem mixedSingularCapHomology_apply (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of R R) X p)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    mixedSingularCapHomology X p q c z =
      Products.CapBoundary.singularCapHomology X p q c (IntegralHomologyCoefficients.integralToScalarSingularHomology X (p + q) z) := rfl

/-- The pairing on native homology is represented by the actual finite
mixed cap product. -/
@[simp]
theorem mixedSingularCapHomology_class_class (X : TopCat.{0}) (p q : ℕ)
    (c : Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of R R) X p)
    (z : Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (p + q)) :
    mixedSingularCapHomology X p q (Cohomology.Singular.Representatives.singularClass (ModuleCat.of R R) X p c)
        (Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (p + q) z) =
      Cohomology.Singular.ChainRepresentatives.chainClass (Cohomology.Singular.Evaluation.singularScalarChains (R := R) X) q (mixedSingularCapCycles X p q c z) := by
  rw [mixedSingularCapHomology_apply, IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass,
    Products.CapBoundary.singularCapHomology_class_class]
  rfl

end

end OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology
