import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Local

noncomputable section
open Set Metric
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance gradientInteriorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientInteriorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

theorem interior_first_jet_holder_bound
    {Ω K : Set E} (hΩK : Ω ⊆ K) (hΩ : IsOpen Ω)
    {a : E} (ha : a ∈ Ω) {α : ℝ} (hα1 : α ≤ 1) :
    ∃ ρ > 0, ∃ C > 0, ∀ U : C2Holder (F := ℝ) hΩK α,
      ∀ x ∈ closedBall a ρ, x ∈ K → ∀ y ∈ closedBall a ρ, y ∈ K →
      ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
        C*‖U‖*dist x y^α := by
  obtain ⟨r,hr,hrΩ⟩ := Metric.isOpen_iff.mp hΩ a ha
  let ρ := min (r/4) (1/4)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρr : ρ ≤ r/4 := min_le_left _ _
  have hρ1 : ρ ≤ 1/4 := min_le_right _ _
  have hclosure : closure (ball a (2*ρ)) = closedBall a (2*ρ) :=
    closure_ball a (by positivity)
  have hsmall : closedBall a (2*ρ) ⊆ Ω := by
    intro x hx
    apply hrΩ
    have hx' : dist x a ≤ 2*ρ := hx
    change dist x a < r
    linarith
  have hGK : MapsTo (id : E → E) (closure (ball a (2*ρ))) K := by
    rw [hclosure]
    exact fun x hx => hΩK (hsmall hx)
  obtain ⟨C,hC,hbound⟩ := C2Holder.chart_first_jet_holder_bound hΩK isOpen_ball (convex_ball a (2*ρ))
    (by rw [hclosure]; exact isCompact_closedBall _ _)
    (G := id) (P := id) contDiff_id contDiff_id hGK
    (fun x hx => hsmall (ball_subset_closedBall hx))
    (a := a) (ρ := ρ) (by linarith) hα1
    (by intro x hx; rw [hclosure]; exact closedBall_subset_closedBall (by linarith) hx.1)
    (by intro x hx; rfl)
  exact ⟨ρ,hρ,C,hC,hbound⟩

end OAI.Analysis.Normed.Function.Holder.C2Holder
