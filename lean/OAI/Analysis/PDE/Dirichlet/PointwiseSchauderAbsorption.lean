import OAI.Analysis.PDE.Dirichlet.Periodic.JetAbsorption
import OAI.Analysis.PDE.Schauder.Dirichlet.PointwiseSchauderCover

open Set Metric Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]
local instance pointwiseAbsorbFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance pointwiseAbsorbFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance pointwiseAbsorbSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance pointwiseAbsorbSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Periodic C²,α absorption when each point has its own neighborhood and
its own small-error constant. No uniform dependence on the chosen charts
is required: a finite refinement is chosen before the absorption parameter. -/
theorem lattice_C2Holder_norm_absorption_of_pointwise
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 < α) {I : Type*}
    (u : I → E → F) (hup : ∀ i, LatticePeriodic e b (u i))
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (v : I → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α)
    (hv₀ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.value (v i) x = u i x)
    (hv₁ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (v i) x = fderiv ℝ (u i) x)
    (hv₂ : ∀ i x, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (v i) x = fderiv ℝ (fderiv ℝ (u i)) x)
    (N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ x : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
      ∃ ρ > 0, ∀ ε > 0, ∃ D > 0, ∀ i
      (y : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0})),
      dist y x ≤ ρ →
        ‖u i y‖ ≤ ε * ‖v i‖ + D * N i ∧
        ‖fderiv ℝ (u i) y‖ ≤ ε * ‖v i‖ + D * N i ∧
        ‖fderiv ℝ (fderiv ℝ (u i)) y‖ ≤ ε * ‖v i‖ + D * N i ∧
      ∀ z : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
        dist z x ≤ ρ →
          ‖fderiv ℝ (fderiv ℝ (u i)) y - fderiv ℝ (fderiv ℝ (u i)) z‖ ≤
            (ε * ‖v i‖ + D * N i) * dist y z ^ α) :
    ∃ C > 0, ∀ i, ‖v i‖ ≤ C * N i := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨ρ, hρ, huniform⟩ := OAI.Analysis.PDE.Schauder.compact_pointwise_jet_constants
    (fun i (x : S) => u i x)
    (fun i (x : S) => fderiv ℝ (u i) x)
    (fun i (x : S) => fderiv ℝ (fderiv ℝ (u i)) x)
    α (fun i => ‖v i‖) N hN hlocal
  apply lattice_C2Holder_norm_absorption e b hK hr hrp hbounded ρ hρ hα
    u hup v hv₀ hv₁ hv₂ N hN
  intro ε hε
  obtain ⟨D, hD, hb⟩ := huniform ε hε
  exact ⟨D, hD, fun i x y hy => hb i x y hy⟩

end OAI.Analysis.PDE.Dirichlet
