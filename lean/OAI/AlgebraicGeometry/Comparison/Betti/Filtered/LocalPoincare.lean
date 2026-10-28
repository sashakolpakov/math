import OAI.AlgebraicGeometry.Comparison.Betti.FilteredLocalIteration
import OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredLocalPrimitive

/-! # Local Poincare -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LocalPoincare.Hodge

noncomputable section

/-! Actual local exactness of the smooth Hodge-filtered de Rham complex
above its truncation degree, for every integer filtration index. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

omit [FiniteDimensional ℂ E] in
theorem openFormFiltration_antitone (U : Opens M) (n : ℕ) : Antitone (Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n) := by
  intro r s hrs a ha
  exact ManifoldFormFiltration.Hodge.manifoldFormFiltration_antitone E U n hrs ha

omit [FiniteDimensional ℂ E] in
theorem openFormFiltration_eq_top [FiniteDimensional ℝ E]
    (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ 0) : Open.FiltrationDescent.Hodge.openFormFiltration (E := E) U n r = ⊤ := by
  unfold Open.FiltrationDescent.Hodge.openFormFiltration
  rw [ManifoldFormFiltration.Hodge.manifoldFormFiltration_eq_top E U n r hr, Submodule.comap_top]

theorem filtered_local_poincare_nat (U : Opens M) (n p : ℕ) (hp : p ≤ n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1)) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) (p : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ u : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, u ∈ Open.FiltrationDescent.Hodge.openFormFiltration V n (p : ℤ) ∧
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  have hdeg : p + (n + 1 - p) = n + 1 := by omega
  obtain ⟨V, hxV, hV, t, c, htf, hcd, hcf, hsum⟩ :=
    FilteredLocalIteration.Hodge.exists_local_filtered_reduction U n p (n + 1 - p) (by omega) a ha hd x
  rw [hdeg] at hcf
  obtain ⟨W, hxW, hW, u, huf, hu⟩ :=
    TopFilteredLocalPrimitive.Hodge.topFiltered_local_primitive V n (p : ℤ) (by exact_mod_cast hp) c hcf hcd ⟨x, hxV⟩
  refine ⟨W, hxW, hW.trans hV, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hW t + u,
    Submodule.add_mem _ (Open.FiltrationDescent.Hodge.openFormFiltration_restrict hW n _ t htf) huf, ?_⟩
  have hr := congrArg (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (n := n + 1) hW) hsum
  rw [map_add, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans] at hr
  rw [map_add, hu]
  exact (add_comm _ _).trans hr

theorem filtered_local_poincare (U : Opens M) (n : ℕ) (r : ℤ) (hr : r ≤ (n : ℤ))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (n + 1)) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) r)
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) (x : U) :
    ∃ V : Opens M, x.val ∈ V ∧ ∃ hV : V ≤ U,
      ∃ u : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E V n, u ∈ Open.FiltrationDescent.Hodge.openFormFiltration V n r ∧
        Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d u = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hV a := by
  by_cases hr0 : r ≤ 0
  · have : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
    have ha0 : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U (n + 1) 0 := by
      rw [openFormFiltration_eq_top U (n + 1) 0 le_rfl]
      exact Submodule.mem_top
    obtain ⟨V, hxV, hV, u, huf, hu⟩ := filtered_local_poincare_nat U n 0 (Nat.zero_le n) a ha0 hd x
    exact ⟨V, hxV, hV, u, openFormFiltration_antitone V n hr0 huf, hu⟩
  · have hrnonneg : 0 ≤ r := by omega
    lift r to ℕ using hrnonneg
    exact filtered_local_poincare_nat U n r (by exact_mod_cast hr) a ha hd x

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LocalPoincare.Hodge
