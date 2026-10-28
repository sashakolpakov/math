import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.PositiveComplexSphere
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductRealCoordinates

/-! # Combined Complex Sphere Map -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CombinedComplexSphereMap

noncomputable section

/-! The original complex sphere map and generator in the total degrees
of a complex line crossed with a positive-dimensional tangent space. -/

open _root_.CategoryTheory _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def combinedComplexRationalSphereMap (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 2) → ℂ)) 0 (2 * p + 4) ⟶
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (2 * p + 3))).homology (2 * p + 3) := by
  simpa only [Nat.mul_succ] using Rational.PositiveComplexSphere.positiveComplexRationalSphereMap (p + 1)

theorem combinedComplexRationalSphereMap_injective (p : ℕ) :
    Function.Injective (combinedComplexRationalSphereMap p) := by
  simpa only [combinedComplexRationalSphereMap, Nat.mul_succ, id_eq] using
    Rational.PositiveComplexSphere.positiveComplexRationalSphereMap_injective (p + 1)

def combinedComplexRationalGeneratorClass (p : ℕ) :
    CycleClass.Geometric.RelativeScalarChains.Cycles.localScalarHomology ℚ (TopCat.of (Fin (p + 2) → ℂ)) 0 (2 * p + 4) := by
  simpa only [Nat.mul_succ] using
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChains ℚ (TopCat.of (Fin (p + 2) → ℂ)) ({0}ᶜ))
      (2 * (p + 1) + 2) (Rational.PositiveComplexSphere.positiveComplexOrthantRationalCycle (p + 1))

theorem combinedComplexRationalGeneratorClass_sphere (p : ℕ) :
    combinedComplexRationalSphereMap p (combinedComplexRationalGeneratorClass p) =
      Rational.OrthantSphere.rationalOrthantSphereClass (2 * p + 3) := by
  simpa only [combinedComplexRationalSphereMap, combinedComplexRationalGeneratorClass,
    Nat.mul_succ, id_eq] using Rational.PositiveComplexSphere.positiveComplexRationalGenerator_sphere (p + 1)

theorem combinedComplexRationalSphereMap_formula (p : ℕ) :
    combinedComplexRationalSphereMap p =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.relativeScalarChainSequence_shortExact ℚ (TopCat.of (Fin (p + 2) → ℂ)) ({0}ᶜ)).δ
        (2 * p + 4) (2 * p + 3) rfl ≫
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom ⟨CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (Complex.ProductRealCoordinates.combinedComplexRealCoordinates p),
          (CycleClass.Geometric.NormalNormChange.Cycles.puncturedNormalHomeomorph (Complex.ProductRealCoordinates.combinedComplexRealCoordinates p)).continuous⟩)) (2 * p + 3) ≫
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (2 * p + 4)))))) (2 * p + 3) := by
  simp only [combinedComplexRationalSphereMap, Rational.PositiveComplexSphere.positiveComplexRationalSphereMap,
    Complex.ProductRealCoordinates.combinedComplexRealCoordinates, Positive.ComplexCoordinates.positiveComplexRealPuncturedCoordinates, Nat.mul_succ, id_eq]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CombinedComplexSphereMap
