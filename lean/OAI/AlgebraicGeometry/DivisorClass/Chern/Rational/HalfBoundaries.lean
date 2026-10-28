import OAI.AlgebraicGeometry.DivisorClass.Chern.PuncturedHalfBoundary
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.ChainRepresentatives
import OAI.AlgebraicGeometry.DivisorClass.Chern.CrossHalfBoundaryAlgebra

/-! # Half Boundaries -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HalfBoundaries

noncomputable section

/-! The actual supported half-disk boundary identities with rational coefficients. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def rationalPlaneHalfFilling (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 2 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) 2 (PlaneHalfFillings.planeHalfFilling b)

def rationalPlaneHalfOuterChain (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 1 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) 1 (PlaneHalfFillings.planeHalfOuterChain b)

def rationalPlaneHalfAxisChain (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).X 1 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) 1 (PlaneHalfFillings.planeHalfAxisChain b)

def rationalPlaneHalfOuterPuncturedChain (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b))).X 1 :=
  ChainRepresentatives.rationalSingularChainElement (TopCat.of (PlaneProductCharts.PuncturedPlaneHalf b)) 1 (PuncturedHalfBoundary.planeHalfOuterPuncturedChain b)

theorem rationalPlaneHalfFilling_boundary (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 2 1
      (rationalPlaneHalfFilling b) =
      rationalPlaneHalfOuterChain b - (OrthantSphereEquator.orthantSign b : ℚ) • rationalPlaneHalfAxisChain b := by
  rw [rationalPlaneHalfFilling, ChainRepresentatives.rationalSingularChainElement_d, PlaneHalfFillings.planeHalfFilling_boundary,
    ChainRepresentatives.rationalSingularChainElement_sub, ChainRepresentatives.rationalSingularChainElement_zsmul, Int.cast_smul_eq_zsmul]
  rfl

theorem rationalPlaneHalfOuterChain_boundary (b : Bool) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 1 0
      (rationalPlaneHalfOuterChain b) =
      (OrthantSphereEquator.orthantSign b : ℚ) • (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b))).d 1 0
        (rationalPlaneHalfAxisChain b) := by
  rw [rationalPlaneHalfOuterChain, rationalPlaneHalfAxisChain, ChainRepresentatives.rationalSingularChainElement_d,
    ChainRepresentatives.rationalSingularChainElement_d, PlaneHalfFillings.planeHalfOuterChain_boundary, PlaneHalfFillings.planeHalfAxisChain_boundary,
    ChainRepresentatives.rationalSingularChainElement_zsmul, Int.cast_smul_eq_zsmul]

theorem rationalPlaneHalfOuterPuncturedChain_inclusion (b : Bool) :
    ((CycleClass.Geometric.RelativeScalarChains.Cycles.scalarSingularChainFunctor ℚ).map (PuncturedHalfBoundary.puncturedPlaneHalfInclusion b)).f 1
      (rationalPlaneHalfOuterPuncturedChain b) = rationalPlaneHalfOuterChain b := by
  rw [rationalPlaneHalfOuterPuncturedChain, ChainRepresentatives.rationalSingularChainElement_map,
    PuncturedHalfBoundary.planeHalfOuterPuncturedChain_inclusion]
  rfl

/-- The cancellation formula now applies to the actual constructed
half-disk chains, with their proved boundary and prescribed sign. -/
theorem rationalPlaneHalfProduct_boundary (b : Bool) (Y : TopCat.{0}) (q : ℕ)
    (B : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X (q + 2))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).X (q + 1))
    (hB : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).d (q + 2) (q + 1) B = z)
    (hz : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) Y).d (q + 1) q z = 0) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × Y))).d (q + 3) (q + 2)
        (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) Y 1 (q + 2) (q + 3) (by omega)
            (rationalPlaneHalfOuterChain b) B +
          Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) Y 2 (q + 1) (q + 3) (by omega)
            (rationalPlaneHalfFilling b) z) =
      (OrthantSphereEquator.orthantSign b : ℚ) •
        (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (TopCat.of (PlaneHalf.coordinatePlaneHalf b × Y))).d (q + 3) (q + 2)
          (Singular.CrossBoundary.singularCrossChain ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) Y 1 (q + 2) (q + 3) (by omega)
            (rationalPlaneHalfAxisChain b) B) :=
  CrossHalfBoundaryAlgebra.singularCrossChain_halfDisk_boundary ℚ (TopCat.of (PlaneHalf.coordinatePlaneHalf b)) Y q (OrthantSphereEquator.orthantSign b : ℚ)
    (rationalPlaneHalfFilling b) (rationalPlaneHalfOuterChain b) (rationalPlaneHalfAxisChain b) B z
    (rationalPlaneHalfFilling_boundary b) (rationalPlaneHalfOuterChain_boundary b) hB hz

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HalfBoundaries
