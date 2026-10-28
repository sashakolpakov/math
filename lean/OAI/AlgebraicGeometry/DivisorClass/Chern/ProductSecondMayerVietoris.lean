import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.HalfSphereBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Axis.ZeroNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SphereAssembly

/-! # Product Second Mayer Vietoris -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSecondMayerVietoris

noncomputable section

/-!
# ChernClass: the second native sphere boundary for the axis half-products

The two actual half-interval products have opposite zero-point
boundaries. Their assembled class maps to the negative tangent
sphere class under the original overlap retraction.
-/

open _root_.CategoryTheory
open _root_.HomologicalComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (r q : ℕ)
variable (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).X (q + 2))
variable (z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
  (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1))
variable (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (EuclideanSpace ℝ (Fin (r + 1))))).d
  (q + 2) (q + 1) B =
    (CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSubspaceChainInclusion ℚ (TopCat.of (EuclideanSpace ℝ (Fin (r + 1)))) ({0}ᶜ)).f (q + 1) z.val)

def axisHalfSpherePieces : Rational.SphereAssembly.SphereRationalChainPieces r (q + 1) where
  left := Axis.HalfSphereBoundary.axisHalfSphereChain r false q B z.val
  right := Axis.HalfSphereBoundary.axisHalfSphereChain r true q B z.val
  overlap := Axis.ZeroNormalization.axisZeroOverlapCycle r (q + 1) z
  left_boundary := by
    have hz := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ q z.val).mp z.property
    have h := Axis.HalfSphereBoundary.axisHalfSphereChain_boundary r false q B z.val hB hz
    change _ = (-1 : ℚ) • _ at h
    rw [neg_one_smul] at h
    exact h
  right_boundary := by
    have hz := (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.mem_chainCycles_iff_succ _ q z.val).mp z.property
    have h := Axis.HalfSphereBoundary.axisHalfSphereChain_boundary r true q B z.val hB hz
    change _ = (1 : ℚ) • _ at h
    rw [one_smul] at h
    exact h

def axisHalfSphereClass : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1))).homology (q + 2) :=
  (axisHalfSpherePieces r q B z hB).sphereClass

theorem axisHalfSphereClass_boundary :
    AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1)))
      (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) (q + 1)
      (axisHalfSphereClass r q B z hB) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (OrthantBoundaryRepresentatives.orthantSphereOverlap r)) (q + 1)
        (-(Axis.ZeroNormalization.axisZeroOverlapCycle r (q + 1) z)) :=
  (axisHalfSpherePieces r q B z hB).sphereClass_boundary

theorem axisHalfSphereClass_lowerSphere :
    homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
      (TopCat.ofHom (CycleClass.Geometric.SphereCover.Cycles.standardSphereOverlapEquiv (r + 1)).toFun)) (q + 1)
      (AlgebraicTopology.Duality.Poincare.RationalHomologyMayerVietoris.rationalMayerVietorisBoundary (CycleClass.Geometric.SphereHomologyInduction.Cycles.standardSphere (r + 1))
        (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1)))
        (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen (-CycleClass.Geometric.SphereCover.Cycles.standardSphereNorthPole (r + 1)))
        (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.isOpen_spherePoleOpen _) (CycleClass.Geometric.SphereCover.Cycles.spherePoleOpen_union _) (q + 1)
        (axisHalfSphereClass r q B z hB)) =
      -(homologyMap ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map
        (TopCat.ofHom (CycleClass.Geometric.NormalSphere.Cycles.normalSphereProjection (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ)
          (TopCat.of (CycleClass.Geometric.NormalSphere.Cycles.PuncturedNormal (EuclideanSpace ℝ (Fin (r + 1)))))) (q + 1) z)) := by
  rw [axisHalfSphereClass_boundary, map_neg, map_neg, Axis.ZeroNormalization.axisZeroOverlapCycle_lowerSphere]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ProductSecondMayerVietoris
