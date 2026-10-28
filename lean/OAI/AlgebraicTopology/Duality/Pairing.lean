import OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Pairing -/

namespace OAI.AlgebraicTopology.Duality.Pairing.Constructions.Poincare

noncomputable section

/-! PoincarePairing: the genuine cup pairing and its algebraic relation to the cap map. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
open OAI.AlgebraicTopology.Duality.Poincare.MixedCapHomology

def fundamentalCap (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q)) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p →ₗ[ℚ]
      (Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology q :=
  (LinearMap.applyₗ' ℚ z).comp (Poincare.MixedCapHomology.mixedSingularCapHomology (R := ℚ) X p q)

def fundamentalPairing (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q))
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) : ℚ :=
  Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) X (p + q)
    (Products.CupCohomology.singularCohomologyCup X p q a b)
    (Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (p + q) z)

theorem fundamentalPairing_eq_evaluation (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q))
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q) :
    fundamentalPairing X p q z a b =
      Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) X q b
        (fundamentalCap X p q z a) :=
  Products.CapCompatibility.singularCohomologyCup_evaluation_cap X p q a b
    (Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℚ) X (p + q) z)

/-- Injectivity of the actual cap map implies left nondegeneracy. -/
theorem fundamentalPairing_left_of_cap_injective
    (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q))
    (hcap : Function.Injective (fundamentalCap X p q z))
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X p)
    (ha : ∀ b, fundamentalPairing X p q z a b = 0) : a = 0 := by
  apply hcap
  rw [map_zero]
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro f
  obtain ⟨b, rfl⟩ := (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) X q).surjective f
  exact (fundamentalPairing_eq_evaluation X p q z a b).symm.trans (ha b)

/-- Surjectivity of the actual cap map implies right nondegeneracy. -/
theorem fundamentalPairing_right_of_cap_surjective
    (X : TopCat.{0}) (p q : ℕ)
    (z : (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology (p + q))
    (hcap : Function.Surjective (fundamentalCap X p q z))
    (b : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X q)
    (hb : ∀ a, fundamentalPairing X p q z a b = 0) : b = 0 := by
  apply (Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) X q).injective
  rw [map_zero]
  apply LinearMap.ext
  intro c
  obtain ⟨a, rfl⟩ := hcap c
  exact (fundamentalPairing_eq_evaluation X p q z a b).symm.trans (hb a)

end

end OAI.AlgebraicTopology.Duality.Pairing.Constructions.Poincare
