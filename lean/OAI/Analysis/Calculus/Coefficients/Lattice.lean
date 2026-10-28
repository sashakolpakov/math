import OAI.Analysis.Calculus.Coefficients.Elliptic

open Set Filter Metric Module
open scoped Topology
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet

variable {E P V F ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [Fintype ι]

theorem tendstoUniformlyOn_nat_add {X Y : Type*} [PseudoMetricSpace Y]
    {u : ℕ → X → Y} {f : X → Y} {S : Set X}
    (h : TendstoUniformlyOn u f atTop S) (N : ℕ) :
    TendstoUniformlyOn (fun j ↦ u (N+j)) f atTop S := by
  refine Metric.tendstoUniformlyOn_iff.mpr ?_
  intro ε hε
  obtain ⟨M,hM⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.mp h ε hε)
  exact eventually_atTop.2 ⟨M,fun j hj ↦ hM (N+j) (by omega)⟩

omit [ProperSpace E] in
theorem periodic_tendstoUniformlyOn_sublevel
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hr : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r) (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : ℕ → E → F) (f : E → F)
    (hu : ∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j)) (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    (hc : TendstoUniformlyOn u f atTop (OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r)) :
    TendstoUniformlyOn u f atTop {x | r x ≤ 0} := by
  refine Metric.tendstoUniformlyOn_iff.mpr ?_
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hc ε hε] with j hj
  intro x hx
  have h := hj (OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b x)
    (OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hr hbounded hx)
  rwa [hf.representative,(hu j).representative] at h

theorem periodic_global_bound_holder_of_compact_bounds
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} {r : E → ℝ}
    (hK : IsCompact K) (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (u : ℕ → E → F) (hu : ∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j))
    {α : ℝ} (hα : 0 ≤ α)
    (hb : ∀ S : Set E, IsCompact S → ∃ C : ℝ, 0 < C ∧
      (∀ j x, x ∈ S → ‖u j x‖ ≤ C) ∧
      (∀ j x, x ∈ S → ∀ y, y ∈ S → ‖u j x-u j y‖ ≤ C*dist x y^α)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ j x, r x ≤ 0 → ‖u j x‖ ≤ C) ∧
      (∀ j x, r x ≤ 0 → ∀ y, r y ≤ 0 → ‖u j x-u j y‖ ≤ C*dist x y^α) := by
  let S := OAI.Analysis.PDE.Dirichlet.latticeSublevelCell e b K r
  have hS : IsCompact S := OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hK hr
  obtain ⟨C,hC,hCB,hCH⟩ := hb (cthickening 1 S) hS.cthickening
  have hsub : S ⊆ cthickening 1 S := by
    intro x hx
    exact ((closedBall_subset_cthickening_singleton x 1).trans
      (cthickening_subset_of_subset 1 (singleton_subset_iff.mpr hx))) (by simp)
  have hB j x (hx : r x ≤ 0) : ‖u j x‖ ≤ C := by
    rw [← (hu j).representative x]
    exact hCB j _ (hsub (OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrp hbounded hx))
  have hH := OAI.Analysis.PDE.Dirichlet.lattice_holder_of_thickened_cell e b hrp hbounded u hu hα hC.le hC.le hB
    (fun j x hx y hy ↦ hCH j x hx.1 y hy.1)
  refine ⟨C+2*C,by positivity,?_,hH⟩
  intro j x hx
  exact (hB j x hx).trans (by linarith)

end OAI.Analysis.Calculus.Coefficients
