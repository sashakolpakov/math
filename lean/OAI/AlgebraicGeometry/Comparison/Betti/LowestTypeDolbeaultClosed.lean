import OAI.AlgebraicGeometry.Comparison.Betti.Open.PureDifferential
import OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationStep

/-! # Lowest Type Dolbeault Closed -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LowestTypeDolbeaultClosed.Hodge

noncomputable section

/-! The lowest allowed type of a closed filtered form is closed for
the actual Dolbeault differential. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem lowestType_dolbeault_closed (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n (i.val.1 : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) :
    DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD i.val.1 i.val.2 n (Open.FiltrationDescent.Hodge.openTypeProjection U n i a) = 0 := by
  have hr := Open.FiltrationStep.Hodge.openTypeRemainder_filtered U n i a ha
  have hdr := Open.FiltrationDescent.Hodge.openFormFiltration_d n ((i.val.1 : ℤ) + 1) _ hr
  have hz := (Open.FiltrationDescent.Hodge.mem_openFormFiltration_iff_projections U (n + 1) ((i.val.1 : ℤ) + 1) _).mp hdr
    (Analysis.HodgeTheory.Decomposition.Dolbeault.Constructions.advanceAntiholomorphic i) (by
      change (i.val.1 : ℤ) < (i.val.1 : ℤ) + 1
      omega)
  rw [map_add, map_smul, hd, zero_add, map_smul,
    Open.PureDifferential.Hodge.openTypeProjection_d_doublePrime U n i _ (Open.ChartEvaluation.Hodge.openTypeProjection_pure U n i a)] at hz
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  have hv := congrArg (fun b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1) => b x v) hz
  change (-1 : ℂ) * DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD i.val.1 i.val.2 n (Open.FiltrationDescent.Hodge.openTypeProjection U n i a) x v = 0 at hv
  exact (mul_eq_zero.mp hv).resolve_left (by norm_num)

end

end OAI.AlgebraicGeometry.Comparison.Betti.LowestTypeDolbeaultClosed.Hodge
