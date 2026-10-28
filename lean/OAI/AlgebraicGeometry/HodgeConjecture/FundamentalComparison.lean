import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Fundamental Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.FundamentalComparison.CM.SurfaceConstruction

noncomputable section

/-!
Compare the canonical complex fundamental-class evaluation used by repaired
ThetaCycle with evaluation on rational homology used by the geometric cycle map.
Both are computed from the same integral singular cycles. No identification
with an arbitrary linear functional is assumed.
-/

open _root_.CategoryTheory
open scoped TensorProduct Simplicial

/-- On integral chains, coefficient inclusion changes only rational values
to complex values, and keeps every actual singular simplex fixed. -/
theorem rationalCochain_integralEvaluation
    (X : TopCat.{0}) (n : ℕ)
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) X).X n)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of ℂ ℂ) n
      ((ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f n c)
      (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℂ) (TopCat.toSSet.obj X) n z) =
      (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n c
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℚ) (TopCat.toSSet.obj X) n z) : ℂ) := by
  let K := TopCat.toSSet.obj X
  have h :
      ((AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of ℂ ℂ) n
        ((ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain X).f n c)).restrictScalars ℤ).comp
          (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℂ) K n) =
      (AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion.restrictScalars ℤ).comp
        (((AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K (ModuleCat.of ℚ ℚ) n c).restrictScalars ℤ).comp
          (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℚ) K n)) := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext K (ModuleCat.of ℤ ℂ)
    intro s
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex]
    erw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex, AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
    exact ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCochain_evaluation X n c s
  exact LinearMap.congr_fun h z

/-- The rational-to-complex coefficient map preserves evaluation on the
same integral homology class, with coefficients extended on both sides. -/
theorem rationalClass_integralEvaluation
    (X : TopCat.{0}) (n : ℕ)
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) X n
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n a)
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) X n z) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X n a
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n z) : ℂ) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X n a
  obtain ⟨w, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) n z
  rw [ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.rationalToComplexCohomology_class,
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass,
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass,
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class, AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class]
  exact rationalCochain_integralEvaluation X n c.val w.val

/-- Native complex evaluation equals the rational-homology interface on
every scalar extension of a rational cohomology class. -/
theorem complexification_integralEvaluation
    (X : TopCat.{0}) (n : ℕ)
    (a : ComplexMultiplication.WeightOne.CM.Complexification (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n))
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) X n
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification X n a)
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) X n z) =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification X n a)
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X n z) := by
  induction a using TensorProduct.inductionOn with
  | add a b ha hb => simp [ha, hb]
  | tmul r a =>
    rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology_smul_rational]
    erw [map_smul, LinearMap.smul_apply, rationalClass_integralEvaluation]
    simp [Algebra.smul_def, mul_comm]

/-- All complex classes on a smooth projective variety satisfy the same
comparison, using the proved finite-dimensional coefficient isomorphism. -/
theorem projective_integralEvaluation (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : X.complexCohomology n)
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (Betti.Scheme.schemePointSpace X.toOver)).homology n) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ) (Betti.Scheme.schemePointSpace X.toOver) n a
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) n z) =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace X.toOver) n a
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) n z) := by
  let : Module.Finite ℚ (X.rationalCohomology n) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite X n
  obtain ⟨b, rfl⟩ := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective (Betti.Scheme.schemePointSpace X.toOver) n a
  exact complexification_integralEvaluation (Betti.Scheme.schemePointSpace X.toOver) n b z

end

end OAI.AlgebraicGeometry.HodgeConjecture.FundamentalComparison.CM.SurfaceConstruction
