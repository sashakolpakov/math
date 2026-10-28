import OAI.Analysis.PDE.Dirichlet.Periodic.SchauderAbsorption
import OAI.Analysis.PDE.Schauder.Dirichlet.PointwiseSchauderCover

open Set Metric Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Pointwise-center small-error estimates control an actual global
periodic Hölder field. Applicable directly to third- and fourth-derivative
tensors, without assuming any uniformity of the chosen chart constants. -/
theorem lattice_holder_norm_absorption_of_pointwise
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    {α : ℝ} (hα : 0 < α) {I : Type*}
    (g : I → E → F) (hg : ∀ i, LatticePeriodic e b (g i))
    (v : I → OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α)
    (hv : ∀ i x, OAI.Analysis.Normed.Function.Holder.HolderMap.value (v i) x = g i x)
    (N : I → ℝ) (hN : ∀ i, 0 ≤ N i)
    (hlocal : ∀ x : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
      ∃ ρ > 0, ∀ ε > 0, ∃ D > 0, ∀ i
      (y : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0})),
      dist y x ≤ ρ → ‖g i y‖ ≤ ε * ‖v i‖ + D * N i ∧
      ∀ z : ↥(cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}),
        dist z x ≤ ρ → ‖g i y-g i z‖ ≤
          (ε * ‖v i‖ + D * N i) * dist y z ^ α) :
    ∃ C > 0, ∀ i, ‖v i‖ ≤ C * N i := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hjet : ∀ x : S, ∃ ρ > 0, ∀ ε > 0, ∃ D > 0, ∀ i,
      OAI.Analysis.PDE.Schauder.JetBoundOnBall
        (fun y : S => g i y) (fun y : S => g i y) (fun y : S => g i y)
        α x ρ (ε * ‖v i‖ + D * N i) := by
    intro x
    obtain ⟨ρ, hρ, h⟩ := hlocal x
    refine ⟨ρ, hρ, ?_⟩
    intro ε hε
    obtain ⟨D, hD, hb⟩ := h ε hε
    refine ⟨D, hD, ?_⟩
    intro i y hy
    obtain ⟨hn, hh⟩ := hb i y hy
    exact ⟨hn, hn, hn, hh⟩
  obtain ⟨ρ, hρ, huniform⟩ := OAI.Analysis.PDE.Schauder.compact_pointwise_jet_constants
    (fun i (x : S) => g i x) (fun i (x : S) => g i x) (fun i (x : S) => g i x)
    α (fun i => ‖v i‖) N hN hjet
  apply lattice_holder_norm_absorption e b hK hr hrp hbounded ρ hρ hα g hg v hv N hN
  intro ε hε
  obtain ⟨D, hD, hb⟩ := huniform ε hε
  exact ⟨D, hD, fun i x y hy => (hb i x y hy).2.2⟩

end OAI.Analysis.PDE.Dirichlet
