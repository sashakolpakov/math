import OAI.Analysis.Calculus.SmoothExtension.Periodic.OpenGluing

/-! Compact parameter bands suffice for smooth periodic gluing on an open
parameter region, without extending through the region's boundary. -/
noncomputable section
open Set Filter Function TopologicalSpace
open scoped Topology ContDiff Manifold
namespace OAI.Analysis.Calculus.SmoothExtension

variable {Z E T : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup T]

omit [FiniteDimensional ℝ E] in
theorem exists_periodic_smooth_on_of_compact_bands
    (L : T →+ E) (θ : E → Z) (hθ : ContDiff ℝ ∞ θ)
    (hθper : ∀ x t, θ (x + L t) = θ x)
    {Ω : Set Z} (hΩ : IsOpen Ω) (K : Set E) (u : E → ℝ)
    (hc : ∀ C : Set Z, IsCompact C → C ⊆ Ω →
      ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ x t, g (x + L t) = g x) ∧
        ∀ x ∈ K, θ x ∈ C → g x = u x) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (θ ⁻¹' Ω) ∧
      (∀ x t, g (x + L t) = g x) ∧ ∀ x ∈ K, θ x ∈ Ω → g x = u x := by
  apply exists_periodic_smooth_on_parameter_region L θ hθ hθper hΩ K u
  intro z hz
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hz)
  have hsub : Metric.closedBall z (r / 2) ⊆ Ω :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrs
  obtain ⟨g, hg, hgp, hge⟩ := hc (Metric.closedBall z (r / 2))
    (isCompact_closedBall _ _) hsub
  exact ⟨Metric.ball z (r / 2), Metric.isOpen_ball,
    Metric.mem_ball_self (by linarith), g, hg, hgp,
    fun x hx ht ↦ hge x hx (Metric.ball_subset_closedBall ht.2)⟩

end OAI.Analysis.Calculus.SmoothExtension
