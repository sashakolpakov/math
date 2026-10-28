import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup
import OAI.Geometry.ComplexTorus.RiemannProjectivity.RationalLoops
import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology
import OAI.AlgebraicTopology.Products.CapCompatibility
import Mathlib.RingTheory.Flat.Basic

/-! # Complex Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ComplexPairing

noncomputable section

/-! The actual complex cup pairing and its compatibility with rational Poincare duality. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory
open scoped TensorProduct

namespace CM.Abelian
open OAI.AlgebraicTopology.Products.CapCompatibility OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

def rationalCupPairing (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q)) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q →ₗ[ℚ] ℚ :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q).compr₂
    ((LinearMap.applyₗ' ℚ z).comp (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (p + q)))

def complexCupPairing (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q)) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X p →ₗ[ℂ]
      AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X q →ₗ[ℂ] ℂ :=
  (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q).compr₂
    ((LinearMap.applyₗ' ℂ z).comp
      (Geometry.ComplexTorus.RiemannProjectivity.RationalLoops.Constructions.Rational.complexEvaluationEquiv X (p + q)).toLinearMap)

theorem complexCupPairing_rational (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q))
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    complexCupPairing X p q z (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X p a)
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X q b) = (rationalCupPairing X p q z a b : ℂ) := by
  change ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X (p + q)
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) X p q (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X p a)
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X q b)) z = _
  rw [← AbelianVariety.ExteriorCohomologyComplexCup.Constructions.rationalToComplex_cup]
  have h := ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology_smul_rational X (p + q) 1
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b) z
  simpa [rationalCupPairing, Algebra.smul_def] using h

section ScalarExtension

variable {V W : Type} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]

def pairingScalarExtension (B : V →ₗ[ℚ] W →ₗ[ℚ] ℚ) :
    (ℂ ⊗[ℚ] V) →ₗ[ℂ] W →ₗ[ℚ] ℂ :=
  (IsBaseChange.linearMapRightBaseChangeEquiv W (IsBaseChange.linearMap ℚ ℂ)).toLinearMap.comp
    (B.baseChange ℂ)

theorem pairingScalarExtension_tmul (B : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (c : ℂ) (v : V) (w : W) :
    pairingScalarExtension B (c ⊗ₜ[ℚ] v) w = c * (B v w : ℂ) := rfl

theorem pairingScalarExtension_injective (B : V →ₗ[ℚ] W →ₗ[ℚ] ℚ)
    (hB : Function.Injective B) : Function.Injective (pairingScalarExtension B) :=
  (IsBaseChange.linearMapRightBaseChangeEquiv W (IsBaseChange.linearMap ℚ ℂ)).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap B hB)

end ScalarExtension

theorem complexCupPairing_complexification_rational (X : TopCat.{0}) (p q : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)]
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q))
    (a : ℂ ⊗[ℚ] AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    complexCupPairing X p q z (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification X p a)
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X q b) =
        pairingScalarExtension (rationalCupPairing X p q z) a b := by
  induction a using TensorProduct.inductionOn with
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul c a =>
    rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, map_smul, LinearMap.smul_apply,
      complexCupPairing_rational, pairingScalarExtension_tmul]
    rfl

theorem complexCupPairing_left_nondegenerate (X : TopCat.{0}) (p q : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)]
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)]
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology (p + q))
    (hB : Function.Injective (rationalCupPairing X p q z))
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X p)
    (ha : ∀ b, complexCupPairing X p q z a b = 0) : a = 0 := by
  obtain ⟨a, rfl⟩ := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective X p a
  have hz : pairingScalarExtension (rationalCupPairing X p q z) a = 0 := by
    ext b
    exact (complexCupPairing_complexification_rational X p q z a b).symm.trans (ha _)
  have ha0 : a = 0 := pairingScalarExtension_injective _ hB
    (hz.trans (map_zero _).symm)
  rw [ha0, map_zero]

theorem complexCupPairing_rational_cap (X : TopCat.{0}) (p q : ℕ)
    [Module.Finite ℚ (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)]
    (z : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q))
    (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) X q) :
    complexCupPairing X p q (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (p + q) z)
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology X p a) b =
        ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X q b (AlgebraicTopology.Duality.Poincare.MixedCapHomology.mixedSingularCapHomology X p q a z) := by
  obtain ⟨b, rfl⟩ := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_surjective X q b
  induction b using TensorProduct.inductionOn with
  | add b c hb hc => simp only [map_add, LinearMap.add_apply, hb, hc]
  | tmul c b =>
    rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, map_smul,
      complexCupPairing_rational, ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology_smul_rational]
    change c * (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (p + q)
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup X p q a b)
      (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology X (p + q) z) : ℂ) = _
    rw [AlgebraicTopology.Products.CapCompatibility.singularCohomologyCup_evaluation_cap]
    change c * (_ : ℂ) = (_ : ℚ) • c
    rw [Algebra.smul_def, mul_comm]
    rfl

theorem evaluateComplexOnRationalHomology_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) (a : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℂ ℂ) Y n)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology n) :
    ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology X n
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a) z =
      ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology Y n a (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f n z) := by
  have hn := ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso_naturality f n)
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).inv a)
  change (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).hom
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).inv a)) =
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n
      ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).hom
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).inv a)) at hn
  have hi : (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℂ) f n
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).inv a) := by
    apply (AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv.injective
    exact ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).toLinearEquiv.apply_symm_apply _).trans
      (((congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n)
        ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso Y n).toLinearEquiv.apply_symm_apply a)).symm).trans hn.symm)
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℂ) X n
    ((AlgebraicTopology.Cohomology.Singular.RationalComplex.complexCohomologyRestrictionIso X n).inv
      (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ) f n a)) z = _
  rw [hi]
  exact AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℂ) f n _ z

end CM.Abelian

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.ComplexPairing
