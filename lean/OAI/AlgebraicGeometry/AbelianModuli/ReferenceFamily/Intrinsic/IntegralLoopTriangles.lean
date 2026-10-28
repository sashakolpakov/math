import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.Loop
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodLoopClasses
import OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference

/-! # Integral Loop Triangles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralLoopTriangles

noncomputable section

/-! The integral two-cycle formed by multiplying two original period
loops. Its horizontal and vertical edges are those same original loops. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory Opposite
open scoped Simplicial _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : CommGroup (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) :=
  inferInstanceAs (CommGroup A.variety.analyticSpace)

theorem singularDegenerateEdge_value (X : TopCat.{0})
    (v : (TopCat.toSSet.obj X) _⦋0⦌) (z : Convexity.StdSimplex ℝ (Fin 2)) :
    X.toSSetObjEquiv (op ⦋1⦌) ((TopCat.toSSet.obj X).σ 0 v) z =
      TopCat.toSSetObj₀Equiv v := by
  let ev := X.toSSetObjEquiv (op ⦋0⦌) v
  change ev _ = ev _
  exact congrArg ev (Subsingleton.elim _ _)

variable (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ m : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)

theorem nativeLoopHorizontalEdge_multiplication :
    (TopCat.toSSet.map (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)).app (op ⦋1⦌)
        (Integral.Loop.loopHorizontalEdge (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
          (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m)) = PeriodLoopClasses.nativePeriodLoop A ℓ := by
  apply ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌) (PeriodLoopClasses.nativePeriodLoop A ℓ) z) *
      ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌)
        ((TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).σ 0
          ((TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).δ 1 (PeriodLoopClasses.nativePeriodLoop A m))) z) = _
  rw [singularDegenerateEdge_value, PeriodLoopClasses.nativePeriodLoop_basepoint]
  exact mul_one _

theorem nativeLoopVerticalEdge_multiplication :
    (TopCat.toSSet.map (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)).app (op ⦋1⦌)
        (Integral.Loop.loopVerticalEdge (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
          (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m)) = PeriodLoopClasses.nativePeriodLoop A m := by
  apply ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌)
        ((TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).σ 0
          ((TopCat.toSSet.obj (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).δ 1 (PeriodLoopClasses.nativePeriodLoop A ℓ))) z) *
      ((AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A).toSSetObjEquiv (op ⦋1⦌) (PeriodLoopClasses.nativePeriodLoop A m) z) = _
  rw [singularDegenerateEdge_value, PeriodLoopClasses.nativePeriodLoop_basepoint]
  exact one_mul _

def nativeLoopTriangleCycle (R : Type) [CommRing R] :
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := R) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 2 :=
  AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := R) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A)) 2
    (Integral.Loop.loopTriangleCycle (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)
      (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m) R
      (PeriodLoopClasses.nativePeriodLoop_closed A ℓ) (PeriodLoopClasses.nativePeriodLoop_closed A m))

def nativeIntegralLoopTriangleClass :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)).homology 2 :=
  AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 2
    (nativeLoopTriangleCycle A ℓ m ℤ)

theorem nativeLoopTriangleCycle_rationalize :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
        (nativeLoopTriangleCycle A ℓ m ℤ) = nativeLoopTriangleCycle A ℓ m ℚ := by
  let B := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointProductTop A
  let X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A
  let f : B ⟶ X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A
  let zI : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains B) 2 :=
    Integral.Loop.loopTriangleCycle X X (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m) ℤ
      (PeriodLoopClasses.nativePeriodLoop_closed A ℓ) (PeriodLoopClasses.nativePeriodLoop_closed A m)
  let zQ : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) B) 2 :=
    Integral.Loop.loopTriangleCycle X X (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m) ℚ
      (PeriodLoopClasses.nativePeriodLoop_closed A ℓ) (PeriodLoopClasses.nativePeriodLoop_closed A m)
  let p := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.chainCycleMap (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularScalarChainMap (R := ℚ) f) 2
  have hn : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X 2
      (nativeLoopTriangleCycle A ℓ m ℤ) =
      p (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) B 2 zI) :=
    (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles_naturality (R := ℚ) f 2 zI).symm
  have hz : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) B 2 zI = zQ :=
    Integral.Loop.loopTriangleCycle_rationalize X X (PeriodLoopClasses.nativePeriodLoop A ℓ) (PeriodLoopClasses.nativePeriodLoop A m)
      (PeriodLoopClasses.nativePeriodLoop_closed A ℓ) (PeriodLoopClasses.nativePeriodLoop_closed A m)
  exact hn.trans (congrArg p hz)

theorem nativeIntegralLoopTriangleClass_rationalize :
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A) 2
        (nativeIntegralLoopTriangleClass A ℓ m) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A)) 2
        (nativeLoopTriangleCycle A ℓ m ℚ) := by
  let X := AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianPointTop A
  let zI : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) 2 := nativeLoopTriangleCycle A ℓ m ℤ
  let zQ : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 2 := nativeLoopTriangleCycle A ℓ m ℚ
  have hz : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X 2 zI = zQ :=
    nativeLoopTriangleCycle_rationalize A ℓ m
  have hn : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X 2
      (nativeIntegralLoopTriangleClass A ℓ m) =
      AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 2
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X 2 zI) :=
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass (R := ℚ) X 2 zI
  exact hn.trans (congrArg (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) 2) hz)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralLoopTriangles
