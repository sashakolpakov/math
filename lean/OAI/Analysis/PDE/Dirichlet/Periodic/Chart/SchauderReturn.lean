import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.SchauderReturnBounds

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A fixed local inverse chart returns the entire local Schauder jet
estimate to physical space. No convexity assumption is imposed on T. -/
theorem exists_chart_schauder_return_bound
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {D S T : Set E} (hDc : IsCompact D) (hDv : Convex ℝ D) (hSv : Convex ℝ S)
    (hTD : T ⊆ D) (hPS : MapsTo P T S)
    (hinv : ∀ x ∈ T, ∀ᶠ y in 𝓝 x, G (P y) = y)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ M : ℝ, 0 ≤ M →
      SchauderJetBoundsOn (fun z ↦ u (G z)) S α M → SchauderJetBoundsOn u T α (C*M) := by
  obtain ⟨C,hC,hcomp⟩ := exists_schauder_composition_bound P hP hDc hDv hSv hTD hPS hα hα1
  refine ⟨C,hC,?_⟩
  intro u hu M hM hb
  have hw : ContDiff ℝ 2 (fun z ↦ u (G z)) := hu.comp (hG.of_le (by norm_num))
  have hbound := hcomp (fun z ↦ u (G z)) hw M hM hb
  apply hbound.congr_germ
  intro x hx
  filter_upwards [hinv x hx] with y hy
  exact congrArg u hy

/-- Open-neighborhood form of the local inverse assumption. -/
theorem exists_chart_schauder_return_bound_of_open
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    {D S T V : Set E} (hDc : IsCompact D) (hDv : Convex ℝ D) (hSv : Convex ℝ S)
    (hTD : T ⊆ D) (hPS : MapsTo P T S) (hV : IsOpen V) (hTV : T ⊆ V)
    (hinv : ∀ x ∈ V, G (P x) = x)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ M : ℝ, 0 ≤ M →
      SchauderJetBoundsOn (fun z ↦ u (G z)) S α M → SchauderJetBoundsOn u T α (C*M) := by
  apply exists_chart_schauder_return_bound G P hG hP hDc hDv hSv hTD hPS _ hα hα1
  intro x hx
  filter_upwards [hV.mem_nhds (hTV hx)] with y hy
  exact hinv y hy

/-- Physical closed-ball version, expanded into the four concrete bounds
used in the global Schauder assembly. The intersection with K need not be convex. -/
theorem exists_closedBall_chart_schauder_return_bound
    (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 3 P)
    (a : E) (R : ℝ) {K S V : Set E} (hSv : Convex ℝ S)
    (hPS : MapsTo P (closedBall a R ∩ K) S) (hV : IsOpen V)
    (hTV : closedBall a R ∩ K ⊆ V) (hinv : ∀ x ∈ V, G (P x) = x)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ M : ℝ, 0 ≤ M →
      (∀ z ∈ S, |u (G z)| ≤ M) →
      (∀ z ∈ S, ‖fderiv ℝ (fun y ↦ u (G y)) z‖ ≤ M) →
      (∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ (fun y ↦ u (G y))) z‖ ≤ M) →
      (∀ x ∈ S, ∀ y ∈ S,
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ u (G z))) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ u (G z))) y‖ ≤ M*‖x-y‖^α) →
      (∀ x ∈ closedBall a R ∩ K, |u x| ≤ C*M) ∧
      (∀ x ∈ closedBall a R ∩ K, ‖fderiv ℝ u x‖ ≤ C*M) ∧
      (∀ x ∈ closedBall a R ∩ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C*M) ∧
      (∀ x ∈ closedBall a R ∩ K, ∀ y ∈ closedBall a R ∩ K,
        ‖fderiv ℝ (fderiv ℝ u) x-fderiv ℝ (fderiv ℝ u) y‖ ≤ C*M*‖x-y‖^α) := by
  obtain ⟨C,hC,hreturn⟩ := exists_chart_schauder_return_bound_of_open G P hG hP
    (isCompact_closedBall a R) (convex_closedBall a R) hSv (fun _ hx ↦ hx.1)
    hPS hV hTV hinv hα hα1
  refine ⟨C,hC,?_⟩
  intro u hu M hM h0 h1 h2 hH
  have hh := hreturn u hu M hM ⟨h0,h1,h2,hH⟩
  exact ⟨hh.value,hh.first,hh.second,hh.second_holder⟩

end OAI.Analysis.PDE.Dirichlet
