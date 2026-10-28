import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation

/-! # Filtration Step -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationStep.Hodge

noncomputable section

/-! Removing the lowest allowed type advances the actual smooth Hodge
filtration by one step. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem bidegree_eq_of_first_eq {n : ℕ} (i j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (h : i.val.1 = j.val.1) : i = j := by
  apply Subtype.ext
  apply Prod.ext h
  have hi := i.property
  have hj := j.property
  omega

theorem openFormFiltration_raise (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ FiltrationDescent.Hodge.openFormFiltration U n (i.val.1 : ℤ))
    (hi : FiltrationDescent.Hodge.openTypeProjection U n i a = 0) : a ∈ FiltrationDescent.Hodge.openFormFiltration U n ((i.val.1 : ℤ) + 1) := by
  rw [FiltrationDescent.Hodge.mem_openFormFiltration_iff_projections] at ha ⊢
  intro j hj
  by_cases he : j = i
  · simpa only [he] using hi
  · apply ha
    have hne : j.val.1 ≠ i.val.1 := fun h => he (bidegree_eq_of_first_eq j i h)
    omega

theorem openTypeProjection_idempotent (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    FiltrationDescent.Hodge.openTypeProjection U n i (FiltrationDescent.Hodge.openTypeProjection U n i a) = FiltrationDescent.Hodge.openTypeProjection U n i a :=
  ChartEvaluation.Hodge.openTypeProjection_identity U n i _ (ChartEvaluation.Hodge.openTypeProjection_pure U n i a)

theorem openTypeRemainder_filtered (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ FiltrationDescent.Hodge.openFormFiltration U n (i.val.1 : ℤ)) :
    a + (-1 : ℂ) • FiltrationDescent.Hodge.openTypeProjection U n i a ∈ FiltrationDescent.Hodge.openFormFiltration U n ((i.val.1 : ℤ) + 1) := by
  apply openFormFiltration_raise U n i
  · apply Submodule.add_mem _ ha
    apply Submodule.smul_mem
    exact ChartEvaluation.Hodge.openPureFormsInDegree_mem_filtration U n i _ le_rfl _ (ChartEvaluation.Hodge.openTypeProjection_pure U n i a)
  · rw [map_add, map_smul, openTypeProjection_idempotent]
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    ext v
    change FiltrationDescent.Hodge.openTypeProjection U n i a x v + (-1 : ℂ) * FiltrationDescent.Hodge.openTypeProjection U n i a x v = 0
    ring

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationStep.Hodge
