import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Duality
import OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.CoefficientRestriction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-! # Cohomology Base Change -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM

noncomputable section

/-!
# Complexifying actual rational singular cohomology

When rational cohomology is finite dimensional, the canonical rational to
complex coefficient map spans ordinary complex cohomology. The argument
uses evaluation on an actual finite homology basis, with the existing
scalar-restriction comparison and coefficient maps throughout.
-/

open _root_.CategoryTheory
open scoped TensorProduct

/-- A coefficient map sending `1` to `a` becomes `a` times the rational
coefficient inclusion in ordinary complex singular cohomology. -/
theorem complexCohomologyRestrictionIso_coefficient_span (a : ℂ)
    (X : TopCat.{0}) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
      (AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℂ a)) X n c) =
        a • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n c := by
  have h : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℂ a) :
      ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℂ) =
    ModuleCat.ofHom AlgebraicTopology.Cohomology.Singular.RationalRetraction.rationalInclusion ≫
      ModuleCat.ofHom ((a • LinearMap.id : ℂ →ₗ[ℂ] ℂ).restrictScalars ℚ) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro q
    change q • a = a * (q : ℂ)
    rw [Algebra.smul_def, mul_comm]
    rfl
  rw [h, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap_comp, ConcreteCategory.comp_apply,
    Coefficient.CoefficientRestriction.CM.complexCohomologyRestrictionIso_scalar]
  rfl

local instance (X : TopCat.{0}) (n : ℕ) :
    Module ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n) :=
  Module.compHom _ (algebraMap ℚ ℂ)

local instance (X : TopCat.{0}) (n : ℕ) :
    IsScalarTower ℚ ℂ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n) :=
  IsScalarTower.of_compHom ℚ ℂ _

/-- The canonical coefficient-extension map, with no chosen comparison data. -/
def singularCohomologyComplexification (X : TopCat.{0}) (n : ℕ) :
    ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n →ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n :=
  (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n).hom.liftBaseChange ℂ

@[simp]
theorem singularCohomologyComplexification_tmul (X : TopCat.{0}) (n : ℕ)
    (a : ℂ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    singularCohomologyComplexification X n (a ⊗ₜ[ℚ] c) =
      a • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n c := rfl

/-- Evaluate ordinary complex cohomology on rational homology, using the
canonical scalar-restriction isomorphism and vector-valued evaluation. -/
def evaluateComplexOnRationalHomology (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n →ₗ[ℚ]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n →ₗ[ℚ] ℂ) :=
  (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X n).comp
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv.hom

/-- On scalar multiples of rational classes this is the expected pairing. -/
theorem evaluateComplexOnRationalHomology_smul_rational (X : TopCat.{0}) (n : ℕ)
    (a : ℂ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    evaluateComplexOnRationalHomology X n (a • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n c) z =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X n c z) • a := by
  have h := complexCohomologyRestrictionIso_coefficient_span a X n c
  have hi := congrArg (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv h
  have hi' : (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv
      (a • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n c) =
    AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ ℂ a)) X n c := by
    exact hi.symm.trans ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv.symm_apply_apply _)
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X n
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv
      (a • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X n c)) z = _
  rw [hi', AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient]
  rfl

/-- Finite-dimensional universal coefficients, followed by the base change
of the linear dual, gives the perfect pairing with rational homology. -/
def complexifiedEvaluationEquiv (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)] :
    ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n ≃ₗ[ℂ]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n →ₗ[ℚ] ℂ) := by
  let : Module.Finite ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :=
    Coefficient.Duality.CM.finite_homology_of_finite_cohomology X n
  exact (LinearEquiv.baseChange ℚ ℂ _ _ (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n)).trans
    (IsBaseChange.linearMapRightBaseChangeEquiv _ (IsBaseChange.linearMap ℚ ℂ))

@[simp]
theorem complexifiedEvaluationEquiv_tmul (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)]
    (a : ℂ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    complexifiedEvaluationEquiv X n (a ⊗ₜ[ℚ] c) z =
      (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X n c z) • a := by
  change a * algebraMap ℚ ℂ (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X n c z) = _
  rw [Algebra.smul_def, mul_comm]

/-- Evaluation intertwines the actual cohomology coefficient map and
base change of its rational evaluation pairing. -/
theorem evaluateComplexOnRationalHomology_complexification (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)]
    (x : ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n) :
    evaluateComplexOnRationalHomology X n (singularCohomologyComplexification X n x) =
      complexifiedEvaluationEquiv X n x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a c =>
    ext z
    rw [singularCohomologyComplexification_tmul,
      evaluateComplexOnRationalHomology_smul_rational, complexifiedEvaluationEquiv_tmul]

/-- The canonical extension has no kernel. This proof uses evaluation,
independently of any decomposition into Hodge types. -/
theorem singularCohomologyComplexification_injective (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)] :
    Function.Injective (singularCohomologyComplexification X n) := by
  intro x y h
  apply (complexifiedEvaluationEquiv X n).injective
  rw [← evaluateComplexOnRationalHomology_complexification,
    ← evaluateComplexOnRationalHomology_complexification, h]

/-- Finite-dimensional rational cohomology supplies all ordinary complex
classes by the canonical extension of coefficients. -/
theorem singularCohomologyComplexification_surjective (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)] :
    Function.Surjective (singularCohomologyComplexification X n) := by
  let : Module.Finite ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :=
    Coefficient.Duality.CM.finite_homology_of_finite_cohomology X n
  let b := Module.finBasis ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n)
  intro z
  let c := (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv z
  let v (i : Fin (Module.finrank ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n))) :=
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).symm (b.coord i)
  let a (i : Fin (Module.finrank ℚ ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n))) :=
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X n c (b i)
  refine ⟨∑ i, a i ⊗ₜ[ℚ] v i, ?_⟩
  have hc := Coefficient.Duality.CM.coefficient_expansion_in_homology_basis (ModuleCat.of ℚ ℂ) X n b c
  have hz := congrArg (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom hc
  have hcz : (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom c = z :=
    (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv.apply_symm_apply z
  rw [hcz] at hz
  rw [map_sum] at hz
  simp only [complexCohomologyRestrictionIso_coefficient_span] at hz
  simpa only [map_sum, singularCohomologyComplexification_tmul, a, v] using! hz.symm

/-- Extension of coefficients is an isomorphism whenever rational
cohomology in the specified degree is finite dimensional. -/
def singularCohomologyComplexificationEquiv (X : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n)] :
    ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X n ≃ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X n :=
  LinearEquiv.ofBijective (singularCohomologyComplexification X n)
    ⟨singularCohomologyComplexification_injective X n,
      singularCohomologyComplexification_surjective X n⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange.CM
