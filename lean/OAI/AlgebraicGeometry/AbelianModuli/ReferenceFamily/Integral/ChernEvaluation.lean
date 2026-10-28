import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.IntegralSingularChernClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleForgetCocycleClasses
import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

/-! # Chern Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernEvaluation

noncomputable section

/-! The original rational first Chern class has integer evaluation on
every actual integral singular two-cycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

theorem rationalIntegerCocycle_evaluate_integral (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).X n) :
    AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℤ ℚ) X n
        (ModuleForgetCocycleClasses.rationalIntegerCocycle X n c).val z =
      AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c.val
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n z) := by
  have h : AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℤ ℚ) X n
      (ModuleForgetCocycleClasses.rationalIntegerCocycle X n c).val =
    ((AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X n c.val).restrictScalars ℤ).comp
      (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X n) := by
    apply AlgebraicTopology.Cohomology.Singular.ChainDual.chainFunctional_ext (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℚ)
    intro s
    change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℚ) n
        (ModuleForgetCocycleClasses.rationalIntegerCocycle X n c).val (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (TopCat.toSSet.obj X) s) =
      AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv (TopCat.toSSet.obj X) (ModuleCat.of ℚ ℚ) n c.val
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial (R := ℚ) (TopCat.toSSet.obj X) n
          (AlgebraicTopology.Cohomology.Singular.ChainDual.simplexChain (R := ℤ) (TopCat.toSSet.obj X) s))
    rw [AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSimplicial_simplex, AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex,
      AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_simplex]
    exact ModuleForgetCocycleClasses.rationalIntegerAbelianCochainIso_evaluation X s c.val
  exact LinearMap.congr_fun h z

theorem rationalIntegerCohomologyIso_evaluation (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X (n + 1))
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X).homology (n + 1)) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) X (n + 1)
        ((ModuleForgetCocycleClasses.rationalIntegerCohomologyIso X (n + 1)).hom c) z =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (n + 1) c
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (n + 1) z) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.singularClass_surjective (ModuleCat.of ℚ ℚ) X (n + 1) c
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X) (n + 1) z
  let cZ := ModuleForgetCocycleClasses.rationalIntegerCocycle X (n + 1) c
  let zI : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X) (n + 1) := z
  let zQ := AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularCycles (R := ℚ) X (n + 1) zI
  have hc := ModuleForgetCocycleClasses.rationalIntegerCohomologyIso_class X n c
  have hz : AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (n + 1)
      (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X) (n + 1) z) =
    AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (n + 1) zQ :=
    AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_chainClass (R := ℚ) X (n + 1) zI
  calc
    _ = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) X (n + 1)
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℤ ℚ) X (n + 1) cZ)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X) (n + 1) z) :=
      congrArg (fun v : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℚ) X (n + 1) =>
        AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) X (n + 1) v
          (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) X) (n + 1) z)) hc
    _ = AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℤ ℚ) X (n + 1) cZ.val z.val :=
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class (ModuleCat.of ℤ ℚ) X (n + 1) cZ z
    _ = AlgebraicTopology.Cohomology.Singular.ChainDual.singularDegreewiseChainDualEquiv (ModuleCat.of ℚ ℚ) X (n + 1) c.val
        (AlgebraicTopology.Duality.Poincare.IntegralCapCoefficients.integralToScalarSingular (R := ℚ) X (n + 1) z.val) :=
      rationalIntegerCocycle_evaluate_integral X (n + 1) c z.val
    _ = AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (n + 1)
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c)
        (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X) (n + 1) zQ) :=
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation_class_class (ModuleCat.of ℚ ℚ) X (n + 1) c zQ).symm
    _ = _ := congrArg
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (n + 1)
        (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) X (n + 1) c)) hz.symm

theorem rationalIntegerCohomology_integral_evaluation (Y : TopCat.{0}) (n : ℕ)
    (cQ : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y (n + 1))
    (cI : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℤ) Y (n + 1))
    (he : AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient Y (n + 1) cI =
      (ModuleForgetCocycleClasses.rationalIntegerCohomologyIso Y (n + 1)).hom cQ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) Y).homology (n + 1)) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) Y (n + 1) cQ
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) Y (n + 1) z) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℤ) Y (n + 1) cI z : ℚ) := by
  have h0 := (rationalIntegerCohomologyIso_evaluation Y n cQ z).symm
  have h1 : AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) Y (n + 1)
      ((ModuleForgetCocycleClasses.rationalIntegerCohomologyIso Y (n + 1)).hom cQ) z =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) Y (n + 1)
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient Y (n + 1) cI) z :=
    congrArg (fun c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℤ ℚ) Y (n + 1) =>
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) Y (n + 1) c z) he.symm
  have h2 : AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℚ) Y (n + 1)
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap TorusIntegralInjection.integralRationalCoefficient Y (n + 1) cI) z =
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℤ) Y (n + 1) cI z : ℚ) :=
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient TorusIntegralInjection.integralRationalCoefficient Y (n + 1) cI z
  exact h0.trans (h1.trans h2)

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier)
  [MetrizableSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
  [StronglyLocallyContractibleSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]
  [LocallyPathConnectedSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)]

theorem nativeChernClass_integral_evaluation
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))).homology 2) :
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2
        (Intrinsic.ChernClasses.lineBundleChernClass X L)
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2 z) =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℤ ℤ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2
        (Intrinsic.IntegralSingularChernClass.nativeIntegralSingularChernClass X L) z : ℚ) := by
  exact rationalIntegerCohomology_integral_evaluation
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 1
    (Intrinsic.ChernClasses.lineBundleChernClass X L) (Intrinsic.IntegralSingularChernClass.nativeIntegralSingularChernClass X L)
    (Intrinsic.IntegralSingularChernClass.nativeIntegralSingularChernClass_rationalize X L) z

theorem nativeChernClass_evaluation_is_integer
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℤ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))).homology 2) :
    ∃ k : ℤ, (k : ℚ) =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2
        (Intrinsic.ChernClasses.lineBundleChernClass X L)
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) 2 z) :=
  ⟨_, (nativeChernClass_integral_evaluation X L z).symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernEvaluation
