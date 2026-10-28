import OAI.Analysis.Calculus.SmoothExtension.Periodic.TangentExtension

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet

variable {E I P V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Every finite family of constant directions near an interior point can
be realized by globally smooth periodic fields tangent to the whole boundary. -/
theorem exists_interior_periodic_constant_fields
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {r : E → ℝ}
    (hr : Continuous r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) {a : E} (ha : r a < 0)
    (v : I → E) :
    ∃ ρ > 0, ∃ T : I → E → E,
      closedBall a ρ ⊆ {x | r x < 0} ∧
      (∀ i, ContDiff ℝ ∞ (T i)) ∧ (∀ i, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (T i)) ∧
      (∀ i x, r x = 0 → fderiv ℝ r x (T i x) = 0) ∧
      (∀ i x, x ∈ closedBall a ρ → T i =ᶠ[𝓝 x] fun _ => v i) := by
  classical
  have hU : IsOpen {x | r x < 0} := isOpen_lt hr continuous_const
  have hex (i : I) := exists_latticePeriodic_tangent_extension e lat r hrp hU ha
    (fun _ => v i) contDiff_const (by
      intro x hx hz
      have hneg : r x < 0 := hx
      exact (ne_of_lt hneg hz).elim)
  choose T hT hTp hTtan O hO haO hOU hTO using hex
  let W := {x | r x < 0} ∩ ⋂ i, O i
  have hW : IsOpen W := hU.inter (isOpen_iInter_of_finite hO)
  have haW : a ∈ W := ⟨ha,mem_iInter.mpr haO⟩
  obtain ⟨δ,hδ,hδW⟩ := Metric.isOpen_iff.mp hW a haW
  have hball : closedBall a (δ/2) ⊆ W := by
    intro x hx
    exact hδW (lt_of_le_of_lt hx (half_lt_self hδ))
  refine ⟨δ/2,half_pos hδ,T,fun x hx => (hball hx).1,hT,hTp,hTtan,?_⟩
  intro i x hx
  have hxi : x ∈ O i := mem_iInter.mp (hball hx).2 i
  filter_upwards [(hO i).mem_nhds hxi] with y hy
  exact hTO i hy

end OAI.Analysis.Calculus.SmoothExtension
