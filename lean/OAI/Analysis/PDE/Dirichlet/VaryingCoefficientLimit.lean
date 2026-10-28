import OAI.Analysis.PDE.Dirichlet.Linear.Approximation

open Set Module Filter
open scoped Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α M : ℝ}

local instance varyingFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance varyingFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance varyingSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance varyingSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [Fintype ι] in
/-- Smooth coefficient approximation is allowed as well as smooth data
approximation. The equation passes to the limit through the actual Hessian,
and the full original Hölder exponent and norm bound are retained. -/
theorem exists_linear_dirichlet_solution_of_varying_lowerHalf_limit
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) (hα : 0 ≤ α) (hM : 0 ≤ M)
    (A : ℕ → K → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (A₀ : K → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hA : ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 (A₀ x)))
    (f : ℕ → K → ℝ) (f₀ : K → ℝ)
    (hf : ∀ x, Tendsto (fun j ↦ f j x) atTop (𝓝 (f₀ x)))
    (Φ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hΦ : ∀ j, ‖Φ j‖ ≤ M)
    (hmem : ∀ j, Φ j ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat)
    (heq : ∀ j x, A j x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ j) x) = f j x)
    (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (α / 2))
    (hlim : Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ j)) atTop (𝓝 g)) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖u‖ ≤ M ∧
      u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      (∀ x, A₀ x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u x) = f₀ x) ∧
      OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα u = g := by
  obtain ⟨u, hu, hug⟩ :=
    OAI.Analysis.Normed.Function.Holder.C2Holder.exists_original_exponent_of_lowerHalf_limit hα hM Φ g hΦ hlim
  have hmem' : ∀ j, OAI.Analysis.Normed.Function.Holder.C2Holder.lowerHalf hα (Φ j) ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat := by
    intro j
    exact hmem j
  have hg : g ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat :=
    (OAI.Analysis.Normed.Function.Holder.C2Holder.isClosed_latticeDirichlet e lat).mem_of_tendsto hlim
      (Eventually.of_forall hmem')
  have humem : u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat := by
    rw [← hug] at hg
    exact hg
  refine ⟨u, hu, humem, ?_, hug⟩
  intro x
  have hH : Tendsto (fun j ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ j) x) atTop
      (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x)) := by
    simpa only [OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf] using OAI.Analysis.Normed.Function.Holder.C2Holder.jet_second_tendsto hlim x
  have hcont : Continuous (fun p :
      ((E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ) × (E →L[ℝ] E →L[ℝ] ℝ) ↦ p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hprod := (hcont.tendsto (A₀ x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x)).comp
    ((hA x).prodMk_nhds hH)
  have heqg : A₀ x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative g x) = f₀ x := by
    apply tendsto_nhds_unique hprod
    simpa only [Function.comp_def, heq] using hf x
  simpa only [← hug, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_lowerHalf] using heqg

end OAI.Analysis.PDE.Dirichlet
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance varyingCompactFirstNormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance varyingCompactFirstNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance varyingCompactSecondNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance varyingCompactSecondNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The compactness step for simultaneously smoothed coefficients and
forcing. Existence and the uniform estimate for the smooth problems remain
explicit inputs; no inverse or rough-coefficient solvability is assumed. -/
theorem exists_linear_dirichlet_solution_of_smooth_approximants
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (hrper : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α M : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M)
    (A : ℕ → {x | r x ≤ 0} → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (A₀ : {x | r x ≤ 0} → (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ)
    (hA : ∀ x, Tendsto (fun j ↦ A j x) atTop (𝓝 (A₀ x)))
    (F : ℕ → E → ℝ) (f₀ : {x | r x ≤ 0} → ℝ)
    (hF : ∀ x : {x | r x ≤ 0}, Tendsto (fun j ↦ F j x) atTop (𝓝 (f₀ x)))
    (s : ∀ j, SmoothLinearDirichletSolution e lat hΩD α M (A j) (F j)) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ‖u‖ ≤ M ∧
      u ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      ∀ x, A₀ x (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative u x) = f₀ x := by
  obtain ⟨g, φ, hφ, hlim⟩ := exists_closed_banach_subsequence e lat hK hr hrper hbounded hreg
    hα hM (fun j ↦ (s j).u) (fun j ↦ (s j).smooth) (fun j ↦ (s j).periodic)
    (fun j ↦ (s j).jet) (fun j ↦ (s j).bound) (fun j ↦ (s j).value)
    (fun j ↦ (s j).first) (fun j ↦ (s j).second)
  obtain ⟨u, hu, humem, hueq, _⟩ := exists_linear_dirichlet_solution_of_varying_lowerHalf_limit
    e lat hα.le hM (fun j ↦ A (φ j)) A₀
    (fun x ↦ (hA x).comp hφ.tendsto_atTop)
    (fun j x ↦ F (φ j) x) f₀ (fun x ↦ (hF x).comp hφ.tendsto_atTop)
    (fun j ↦ (s (φ j)).jet) (fun j ↦ (s (φ j)).bound)
    (fun j ↦ (s (φ j)).dirichlet) (fun j ↦ (s (φ j)).equation) g hlim
  exact ⟨u, hu, humem, hueq⟩

end OAI.Analysis.PDE.Dirichlet
