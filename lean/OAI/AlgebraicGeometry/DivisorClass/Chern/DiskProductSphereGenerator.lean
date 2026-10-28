import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereBoundaryInjective
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.OrthantSphere
import OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings

/-! # Disk Product Sphere Generator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DiskProductSphereGenerator

noncomputable section

section

/-!
# ChernClass: the actual disk product has the original orthant sphere class

The hypothesis specifies only the tangent boundary class. The disk product
is the previously constructed native chain, and injectivity of both native
boundaries proves its class equals the explicit rational orthant sphere.
-/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem diskProductSphere_eq_orthant (r : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).X (r + 2))
    (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).d
      (r + 2) (r + 1) B =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ)).f (r + 1) z.val)
    (hz : homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1) z) =
        Rational.OrthantSphere.rationalOrthantSphereClass (r + 1)) :
    ProductHalfBoundary.halfProductSphereClass (r + 2) r B z.val hB
      ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ r z.val).mp z.property) =
      Rational.OrthantSphere.rationalOrthantSphereClass (r + 3) := by
  apply Rational.SphereBoundaryInjective.rationalSphereLowerMap_injective (r + 2) (r + 2)
  apply Rational.SphereBoundaryInjective.rationalSphereLowerMap_injective (r + 1) (r + 1)
  rw [ProductDoubleBoundary.diskProductSphere_doubleBoundary (r + 1) r B z hB, hz,
    Rational.OrthantSphere.rationalOrthantSphereClass_lowerSphere, map_neg,
    Rational.OrthantSphere.rationalOrthantSphereClass_lowerSphere, neg_neg]

end

/-! An actual Euclidean filling of the explicit orthant sphere, with its
rational boundary and the disk-product generator theorem specialized to it. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.CycleClass.Geometric.SimplexFillings.Cycles
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def euclideanOrthantPuncturedCycle (r : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1) :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map
    (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereInclusion (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1)
    (OrthantSphereCycle.orientedOrthantSphereCycle (r + 1))

theorem exists_euclideanOrthantFilling (r : ℕ) :
    ∃ B : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).X (r + 2),
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).d (r + 2) (r + 1) B =
        (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ)).f (r + 1)
          (euclideanOrthantPuncturedCycle r).val :=
  CycleClass.Geometric.SimplexFillings.Cycles.exists_singularBoundary_of_contractible (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))
    (r + 1) (Nat.succ_ne_zero r)
    (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ))
      (r + 1) (euclideanOrthantPuncturedCycle r))

def euclideanOrthantFilling (r : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).X (r + 2) :=
  (exists_euclideanOrthantFilling r).choose

theorem euclideanOrthantFilling_boundary (r : ℕ) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).d (r + 2) (r + 1)
      (euclideanOrthantFilling r) =
      (CycleClass.Geometric.LocalHomology.Cycles.subspaceChainInclusion (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ)).f (r + 1)
        (euclideanOrthantPuncturedCycle r).val :=
  (exists_euclideanOrthantFilling r).choose_spec

def euclideanOrthantRationalFilling (r : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).X (r + 2) :=
  Rational.ChainRepresentatives.rationalSingularChainElement _ (r + 2) (euclideanOrthantFilling r)

def euclideanOrthantRationalPuncturedCycle (r : ℕ) :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
      (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1) :=
  Rational.ChainRepresentatives.rationalSingularCycle _ (r + 1) (euclideanOrthantPuncturedCycle r)

theorem euclideanOrthantRationalFilling_boundary (r : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 2))))).d (r + 2) (r + 1)
      (euclideanOrthantRationalFilling r) =
      (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ)).f (r + 1)
        (euclideanOrthantRationalPuncturedCycle r).val := by
  rw [euclideanOrthantRationalFilling, Rational.ChainRepresentatives.rationalSingularChainElement_d, euclideanOrthantFilling_boundary]
  exact (Rational.ChainRepresentatives.rationalSingularChainElement_map
    (CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion (TopCat.of (EuclideanSpace ℝ (Fin (r + 2)))) ({0}ᶜ))
    (r + 1) (euclideanOrthantPuncturedCycle r).val).symm

theorem euclideanOrthantRationalPuncturedCycle_radial (r : ℕ) :
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
        (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1)
          (euclideanOrthantRationalPuncturedCycle r)) = Rational.OrthantSphere.rationalOrthantSphereClass (r + 1) := by
  have he : euclideanOrthantRationalPuncturedCycle r =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereInclusion (EuclideanSpace ℝ (Fin (r + 2)))))) (r + 1)
          (Rational.OrthantSphere.rationalOrthantSphereCycle (r + 1)) :=
    (Rational.OrthantSphere.rationalSingularCycle_map
      (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereInclusion (EuclideanSpace ℝ (Fin (r + 2)))))
      (r + 1) (OrthantSphereCycle.orientedOrthantSphereCycle (r + 1))).symm
  rw [he]
  erw [← AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainClass_naturality ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
    (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereInclusion (EuclideanSpace ℝ (Fin (r + 2))))))
    (r + 1) (Rational.OrthantSphere.rationalOrthantSphereCycle (r + 1))]
  exact (CycleClass.Geometric.NormalSphereHomology.Cycles.normalSphereSingularHomologyIso (EuclideanSpace ℝ (Fin (r + 2)))
    (ModuleCat.of ℚ ℚ) (r + 1)).inv_hom_id_apply (Rational.OrthantSphere.rationalOrthantSphereClass (r + 1))

theorem euclideanOrthantDiskProductSphere_eq_generator (r : ℕ) :
    ProductHalfBoundary.halfProductSphereClass (r + 2) r (euclideanOrthantRationalFilling r)
      (euclideanOrthantRationalPuncturedCycle r).val (euclideanOrthantRationalFilling_boundary r)
      ((AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ r _).mp (euclideanOrthantRationalPuncturedCycle r).property) =
      Rational.OrthantSphere.rationalOrthantSphereClass (r + 3) :=
  diskProductSphere_eq_orthant r (euclideanOrthantRationalFilling r)
    (euclideanOrthantRationalPuncturedCycle r) (euclideanOrthantRationalFilling_boundary r)
    (euclideanOrthantRationalPuncturedCycle_radial r)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DiskProductSphereGenerator
