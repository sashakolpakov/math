import OAI.AlgebraicGeometry.DivisorClass.Chern.SphereAssemblyChains
import OAI.AlgebraicGeometry.DivisorClass.Chern.OrthantSmallComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ChainRepresentatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProductDoubleBoundary

/-! # Orthant Sphere -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.OrthantSphere

noncomputable section

/-!
# ChernClass: actual rational orthant spheres and their native boundaries

Coefficient change transports the explicit integral hemisphere chains.
The resulting native rational assembly is the original orthant sphere
with rational coefficients, and its boundary is the negative lower sphere.
-/

open _root_.CategoryTheory
open _root_.HomologicalComplex
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem rationalSingularChainElement_neg (X : TopCat.{0}) (n : ℕ)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    ChainRepresentatives.rationalSingularChainElement X n (-z) = -ChainRepresentatives.rationalSingularChainElement X n z := by
  simp only [ChainRepresentatives.rationalSingularChainElement, TensorProduct.tmul_neg, map_neg]

theorem rationalSingularCycle_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map f) n (ChainRepresentatives.rationalSingularCycle X n z) =
      ChainRepresentatives.rationalSingularCycle Y n (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) n z) := by
  apply Subtype.ext
  exact ChainRepresentatives.rationalSingularChainElement_map f n z.val

def rationalOrthantSphereCycle (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)) n :=
  ChainRepresentatives.rationalSingularCycle (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n) n (OrthantSphereCycle.orientedOrthantSphereCycle n)

def rationalOrthantSphereClass (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)).homology n :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (rationalOrthantSphereCycle n)

def rationalOrthantSpherePieces (n : ℕ) : SphereAssembly.SphereRationalChainPieces n n where
  left := ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantFirstChart n) (n + 1) (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n)
  right := ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantSecondChart n) (n + 1) (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)
  overlap := ChainRepresentatives.rationalSingularCycle (OrthantBoundaryRepresentatives.orthantSphereOverlap n) n (OrthantSmallCycle.orthantEquatorCycle n)
  left_boundary := by
    rw [ChainRepresentatives.rationalSingularChainElement_d, OrthantBoundaryRepresentatives.orthantFirstHemisphereChain_boundary,
      rationalSingularChainElement_neg]
    change -ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantFirstChart n) n
      ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion n)).f n (OrthantBoundaryRepresentatives.orthantEquatorChain n)) =
      -((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantBoundaryRepresentatives.orthantOverlapFirstInclusion n)).f n
        (ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantSphereOverlap n) n (OrthantSmallCycle.orthantEquatorCycle n).val)
    rw [OrthantSmallCycle.orthantEquatorCycle_val, ChainRepresentatives.rationalSingularChainElement_map]
  right_boundary := by
    rw [ChainRepresentatives.rationalSingularChainElement_d, OrthantBoundaryRepresentatives.orthantSecondHemisphereChain_boundary]
    change ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantSecondChart n) n
      ((CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion n)).f n (OrthantBoundaryRepresentatives.orthantEquatorChain n)) =
      ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantBoundaryRepresentatives.orthantOverlapSecondInclusion n)).f n
        (ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantSphereOverlap n) n (OrthantSmallCycle.orthantEquatorCycle n).val)
    rw [OrthantSmallCycle.orthantEquatorCycle_val, ChainRepresentatives.rationalSingularChainElement_map]

theorem rationalOrthantSpherePieces_ordinaryCycle (n : ℕ) :
    (rationalOrthantSpherePieces n).ordinaryCycle = rationalOrthantSphereCycle (n + 1) := by
  apply Subtype.ext
  rw [SphereAssembly.SphereRationalChainPieces.ordinaryCycle_val]
  change
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).f (n + 1)
      (ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantFirstChart n) (n + 1) (OrthantBoundaryRepresentatives.orthantFirstHemisphereChain n)) +
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (n + 1))))).f (n + 1)
      (ChainRepresentatives.rationalSingularChainElement (OrthantBoundaryRepresentatives.orthantSecondChart n) (n + 1) (OrthantBoundaryRepresentatives.orthantSecondHemisphereChain n)) =
    ChainRepresentatives.rationalSingularChainElement (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (n + 1)) (n + 1) (OrthantSphereCycle.orientedOrthantSphereChain (n + 1))
  rw [ChainRepresentatives.rationalSingularChainElement_map, ChainRepresentatives.rationalSingularChainElement_map,
    ← ChainRepresentatives.rationalSingularChainElement_add, OrthantBoundaryRepresentatives.orthantFirstHemisphereChain_ambient,
    OrthantBoundaryRepresentatives.orthantSecondHemisphereChain_ambient, ← OrthantBoundaryRepresentatives.orientedOrthantSphereChain_split]

theorem rationalOrthantSpherePieces_class (n : ℕ) :
    (rationalOrthantSpherePieces n).sphereClass = rationalOrthantSphereClass (n + 1) := by
  rw [SphereAssembly.SphereRationalChainPieces.sphereClass_eq_ordinaryCycle,
    rationalOrthantSpherePieces_ordinaryCycle]
  rfl

theorem rationalOrthantSphereClass_lowerSphere (n : ℕ) :
    ProductDoubleBoundary.rationalSphereLowerMap n n (rationalOrthantSphereClass (n + 1)) =
      -rationalOrthantSphereClass n := by
  rw [← rationalOrthantSpherePieces_class]
  unfold ProductDoubleBoundary.rationalSphereLowerMap
  rw [ConcreteCategory.comp_apply, SphereAssembly.SphereRationalChainPieces.sphereClass_boundary]
  change homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (n + 1)).toFun)) n
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass _ n (-(ChainRepresentatives.rationalSingularCycle (OrthantBoundaryRepresentatives.orthantSphereOverlap n) n (OrthantSmallCycle.orthantEquatorCycle n)))) = _
  rw [map_neg, map_neg]
  congr 1
  have he : ChainRepresentatives.rationalSingularCycle (OrthantBoundaryRepresentatives.orthantSphereOverlap n) n (OrthantSmallCycle.orthantEquatorCycle n) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantSphereEquator.orderedEquatorOverlap n)) n
        (rationalOrthantSphereCycle n) :=
    (rationalSingularCycle_map (OrthantSphereEquator.orderedEquatorOverlap n) n (OrthantSphereCycle.orientedOrthantSphereCycle n)).symm
  rw [he, ← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality]
  have hm : homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (OrthantSphereEquator.orderedEquatorOverlap n)) n ≫
      homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (n + 1)).toFun)) n =
      𝟙 ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere n)).homology n) := by
    rw [← homologyMap_comp, ← CategoryTheory.Functor.map_comp, OrthantSphereEquator.orderedEquatorOverlap_retraction,
      CategoryTheory.Functor.map_id, homologyMap_id]
    rfl
  exact ConcreteCategory.congr_hom hm (rationalOrthantSphereClass n)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.OrthantSphere
