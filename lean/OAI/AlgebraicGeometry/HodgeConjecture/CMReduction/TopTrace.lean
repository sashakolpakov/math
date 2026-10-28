import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Poincare
import OAI.AlgebraicGeometry.HodgeConjecture.Kunneth
import OAI.AlgebraicTopology.Duality.Poincare.Euclidean

/-! # Top Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TopTrace.CM.Construction

noncomputable section

/-! Top-degree trace on connected projective varieties, using canonical
Poincare duality and the actual cup-product unit. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.Euclidean

open OAI.AlgebraicGeometry.HodgeConjecture.Kunneth.CM.SurfaceConstruction

theorem rationalH0_finrank (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] : Module.finrank ℚ (X.rationalCohomology 0) = 1 := by
  let : PathConnectedSpace (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs
    (PathConnectedSpace X.analyticSpace)
  let : FiniteDimensional ℚ
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)).homology 0) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.projective_homology_finite X.presentation 0
  have h := (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv
    (F := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 0).finrank_eq
  rw [Subspace.dual_finrank_eq] at h
  exact h.trans ((AlgebraicTopology.Duality.Poincare.Euclidean.rationalSingularH0Iso (Betti.Scheme.schemePointSpace X.toOver)).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self ℚ))

theorem rationalUnit_ne_zero (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] : Cycles.Functoriality.UnitCap.cohomologyUnit X ≠ 0 := by
  obtain ⟨a, ha, _⟩ := finrank_eq_one_iff'.mp (rationalH0_finrank X)
  intro hz
  have hunit : AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 0 0
      (Cycles.Functoriality.UnitCap.cohomologyUnit X) a = a :=
    AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace X.toOver)) a
  rw [hz, map_zero, LinearMap.zero_apply] at hunit
  exact ha hunit.symm

theorem rationalH0_smul_unit (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] (a : X.rationalCohomology 0) :
    ∃ r : ℚ, r • Cycles.Functoriality.UnitCap.cohomologyUnit X = a :=
  (finrank_eq_one_iff_of_nonzero' (Cycles.Functoriality.UnitCap.cohomologyUnit X) (rationalUnit_ne_zero X)).mp
    (rationalH0_finrank X) a

def rationalTopEvaluation (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    X.rationalCohomology (2 * X.complexDimension) →ₗ[ℚ] ℚ :=
  (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver)
    (2 * X.complexDimension)).flip (SurfaceConstructionQ.CM.fundamentalQ X)

theorem pairing_unit_top (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : X.rationalCohomology (2 * X.complexDimension)) :
    IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing (Poincare.CM.Construction.nativePoincareData X) (Nat.zero_add _)
      (Cycles.Functoriality.UnitCap.cohomologyUnit X) a = rationalTopEvaluation X a := by
  change rationalTopEvaluation X
    (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCast (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace X.toOver))
      (ModuleCat.of ℚ ℚ) (Nat.zero_add _)
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace X.toOver)) 0 _
        (AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit _) a)) = _
  rw [AlgebraicTopology.Products.CupCohomologyAlgebra.cohomologyCupUnit_cup]

theorem rationalTopEvaluation_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] : Function.Injective (rationalTopEvaluation X) := by
  intro a b hab
  apply IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing_ext_right (Poincare.CM.Construction.nativePoincareData X) (Nat.zero_add _)
  intro c
  obtain ⟨r, rfl⟩ := rationalH0_smul_unit X c
  change IntersectionTheory.ProjectionFormula.Cohomology.Construction.integral (Poincare.CM.Construction.nativePoincareData X) _ _
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 0 _
      (r • Cycles.Functoriality.UnitCap.cohomologyUnit X) a) =
    IntersectionTheory.ProjectionFormula.Cohomology.Construction.integral (Poincare.CM.Construction.nativePoincareData X) _ _
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 0 _
        (r • Cycles.Functoriality.UnitCap.cohomologyUnit X) b)
  simp only [map_smul, LinearMap.smul_apply]
  change r • IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing (Poincare.CM.Construction.nativePoincareData X) (Nat.zero_add _)
    (Cycles.Functoriality.UnitCap.cohomologyUnit X) a =
    r • IntersectionTheory.ProjectionFormula.Cohomology.Construction.pairing (Poincare.CM.Construction.nativePoincareData X) (Nat.zero_add _)
      (Cycles.Functoriality.UnitCap.cohomologyUnit X) b
  rw [pairing_unit_top, pairing_unit_top, hab]

theorem rationalTop_finrank (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] :
    Module.finrank ℚ (X.rationalCohomology (2 * X.complexDimension)) = 1 := by
  let : PathConnectedSpace (Betti.Scheme.schemePointSpace X.toOver) := inferInstanceAs
    (PathConnectedSpace X.analyticSpace)
  exact (X.poincareDuality (2 * X.complexDimension) 0 (Nat.add_zero _)).toLinearEquiv.finrank_eq.trans
    ((AlgebraicTopology.Duality.Poincare.Euclidean.rationalSingularH0Iso (Betti.Scheme.schemePointSpace X.toOver)).toLinearEquiv.finrank_eq.trans
      (Module.finrank_self ℚ))

theorem rationalTop_exists_ne_zero (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] :
    ∃ a : X.rationalCohomology (2 * X.complexDimension), a ≠ 0 := by
  obtain ⟨a, ha, _⟩ := finrank_eq_one_iff'.mp (rationalTop_finrank X)
  exact ⟨a, ha⟩

theorem rationalTopIntegral_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace X.analyticSpace] (n : ℕ) (hn : n = 2 * X.complexDimension) :
    Function.Injective (IntersectionTheory.ProjectionFormula.Cohomology.Construction.integral (Poincare.CM.Construction.nativePoincareData X) n hn) := by
  subst n
  exact rationalTopEvaluation_injective X

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.TopTrace.CM.Construction
