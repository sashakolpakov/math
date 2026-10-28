import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalSmoothChart
import OAI.Analysis.Calculus.SmoothExtension.Periodic.ChartFiniteFields
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatchClosure

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Elliptic

variable {E P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "X" => EuclideanSpace ℝ (Fin m)

/-- Smooth flattening and a simultaneous periodic tangent/normal frame,
constructed solely from the regular periodic defining function. -/
theorem exists_periodic_fourth_boundary_chart
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    (e₀ : X ≃ₗᵢ[ℝ] E) (k : Fin m) {r : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r)
    (a : E) (hreg : fderiv ℝ r a ≠ 0) :
    ∃ (c : ℝ) (G Q : E → E) (δ : ℝ) (T : Fin m → E → E),
      0 < c ∧ ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ Q ∧ G 0 = a ∧
      (∀ z ∈ closedBall 0 2,
        ((fun y => Q (G y)) =ᶠ[𝓝 z] id) ∧ r (G z)-r a = -c*(e₀.symm z) k) ∧
      0 < δ ∧ (∀ i, ContDiff ℝ ∞ (T i)) ∧ (∀ i, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (T i)) ∧
      (∀ i, i ≠ k → ∀ x, r x=0 → fderiv ℝ r x (T i x)=0) ∧
      (∀ i z, z ∈ closedBall 0 δ →
        T i =ᶠ[𝓝 (G z)] OAI.Analysis.PDE.Elliptic.chartTangentField G Q (e₀ (EuclideanSpace.single i 1))) := by
  obtain ⟨c,G,Q,hc,hG,hQ,hG0,hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_physical_smooth_coordinate_chart e₀ k hr a hreg
  have h0 : (0 : E) ∈ closedBall 0 2 := mem_closedBall_self (by norm_num)
  let ℓ : E →L[ℝ] ℝ := (-c) •
    ((EuclideanSpace.proj k).comp e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = ℓ z := fun z hz => (hchart z hz).2
  have hv (i : Fin m) (hi : i ≠ k) : ℓ (e₀ (EuclideanSpace.single i 1)) = 0 := by
    simp [ℓ,Ne.symm hi]
  obtain ⟨δ,hδ,_,T,hT,hTp,htan,hTg⟩ := exists_latticePeriodic_chart_frame e lat hr hrp
    hG hQ hG0 (hchart 0 h0).1 ℓ hlevel k (fun i => e₀ (EuclideanSpace.single i 1)) hv
  exact ⟨c,G,Q,δ,T,hc,hG,hQ,hG0,hchart,hδ,hT,hTp,htan,hTg⟩

omit [FiniteDimensional ℝ E] in
theorem fourth_positive_chart_properties (e₀ : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {r : E → ℝ} {a : E} (hra : r a = 0) {c : ℝ} (hc : 0 < c) (G : E → E)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*(e₀.symm z) k) :
    (closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k) ⊆ closedBall 0 2) ∧
    MapsTo G (closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) {x | r x ≤ 0} ∧
    MapsTo G (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k) {x | r x < 0} := by
  have hclosed (z : E) (hz : z ∈ closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) :
      e₀.symm z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2) := by
    rw [OAI.Analysis.PDE.Elliptic.closure_positiveIsometryHalfPatch] at hz
    exact hz
  have hball (z : E) (hz : z ∈ closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) :
      z ∈ closedBall 0 2 := by
    have hnz : ‖z‖ ≤ (1/2 : ℝ) := by
      simpa only [mem_closedBall,dist_zero_right,e₀.symm.norm_map] using (hclosed z hz).1
    simpa only [mem_closedBall,dist_zero_right] using hnz.trans (by norm_num)
  refine ⟨fun z hz => hball z hz,?_,?_⟩
  · intro z hz
    have he := hlevel z (hball z hz)
    have hp : 0 ≤ e₀.symm z k := (hclosed z hz).2
    change r (G z) ≤ 0
    rw [hra,sub_zero] at he
    nlinarith
  · intro z hz
    have hp : 0 < e₀.symm z k := hz.2
    have he := hlevel z (hball z (subset_closure hz))
    change r (G z) < 0
    rw [hra,sub_zero] at he
    nlinarith

end OAI.Analysis.Calculus.SmoothExtension
