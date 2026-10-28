import OAI.AlgebraicGeometry.Comparison.Betti.Pure.LocalPoincare
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldPurity
import OAI.AlgebraicGeometry.Comparison.Betti.Open.ManifoldRestriction
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback

/-! # Open Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenPoincare

noncomputable section

/-! Local holomorphic primitives in every positive degree on an actual open domain. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E] {U : Opens E} {n : ℕ}

theorem local_open_primitive (a : DeRhamComplex.forms E U (n + 1))
    (ha : DeRhamComplex.differential E U (n + 1) a = 0) (x : U) :
    ∃ (W : Opens E) (hWU : W ≤ U), (x : E) ∈ W ∧ ∃ b : DeRhamComplex.forms E W n,
      DeRhamComplex.differential E W n b =
        HolomorphicPullback.pullback (Opens.inclusion hWU) (contMDiff_inclusion (I := 𝓘(ℂ, E)) hWU) (n + 1) a := by
  let α := (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U (n + 1)).symm (DeRhamComplex.inclusion E U (n + 1) a)
  have hclosed : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d α = 0 := by
    dsimp only [α]
    rw [← Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv_symm_d, ← DeRhamComplex.inclusion_differential, ha, map_zero, map_zero]
  have hpure : ∀ y : U, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (α y) :=
    Open.ManifoldPurity.Holomorphic.smoothOpenManifoldEquiv_symm_pure (p := n + 1) (q := 0)
      (DeRhamComplex.inclusion E U (n + 1) a) a.val.hasManifoldBidegree
  obtain ⟨W, hWU, hx, β, hβ, hβpure⟩ := Pure.LocalPoincare.Holomorphic.pure_local_poincare U α hclosed hpure x
  let bval := Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv W n β
  let bpure : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E W n 0 :=
    ⟨bval, (Open.ManifoldPurity.Holomorphic.smoothOpenManifoldEquiv_pure_iff (p := n) (q := 0) β).mpr hβpure⟩
  have hdb : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d bval =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (Opens.inclusion hWU)
        (contMDiff_inclusion (I := 𝓘(ℝ, E)) hWU) (DeRhamComplex.inclusion E U (n + 1) a) := by
    dsimp only [bval]
    rw [Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv_d, hβ, Open.ManifoldRestriction.Holomorphic.smoothOpenManifoldEquiv_restrict]
    congr 1
    exact (Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U (n + 1)).apply_symm_apply _
  have hhol : bpure ∈ DeRhamComplex.forms E W n := by
    apply (DeRhamComplex.mem_forms_iff_derivative_pure n bpure).mpr
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E W (n + 1) 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d bval).val
    rw [hdb]
    exact a.val.hasManifoldBidegree.pullback (Opens.inclusion hWU)
      (contMDiff_inclusion (I := 𝓘(ℂ, E)) hWU)
  refine ⟨W, hWU, hx, ⟨bpure, hhol⟩, ?_⟩
  apply HolomorphicPullback.inclusion_injective (n + 1)
  rw [DeRhamComplex.inclusion_differential, HolomorphicPullback.pullback_inclusion]
  exact hdb

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.OpenPoincare
