import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalSmoothChart
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Elliptic

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local notation "X" => EuclideanSpace ℝ (Fin m)

/-- A normalized smooth boundary chart between the chosen Euclidean index
space and the physical space. Both inverse germs and physical coverage are
derived from the regularity of the defining function. -/
theorem exists_joint_boundary_chart (j : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {r : E → ℝ} (hr : ContDiff ℝ ∞ r) (a : E)
    (hra : r a = 0) (hreg : fderiv ℝ r a ≠ 0) :
    ∃ (c : ℝ) (G : X → E) (P : E → X),
      0 < c ∧ ContDiff ℝ ∞ G ∧ ContDiff ℝ ∞ P ∧ G 0 = a ∧ P a = 0 ∧
      (∀ x ∈ ball (0 : X) 1,
        (fun y => P (G y)) =ᶠ[𝓝 x] id ∧
        (fun y => G (P y)) =ᶠ[𝓝 (G x)] id ∧ r (G x) = -c * x k) ∧
      ∃ V : Set E, IsOpen V ∧ a ∈ V ∧
        (∀ y ∈ V, G (P y) = y) ∧ MapsTo P V (ball (0 : X) 1) := by
  obtain ⟨c,G₀,P₀,hc,hG₀,hP₀,hGzero,hchart⟩ :=
    exists_physical_smooth_coordinate_chart j k hr a hreg
  have hG3 : ContDiff ℝ 3 G₀ := hG₀.of_le (by simp)
  have hP3 : ContDiff ℝ 3 P₀ := hP₀.of_le (by simp)
  have hzero : (0 : E) ∈ closedBall 0 2 := by simp
  obtain ⟨hPa,R,hR,V,hV,haV,hRV,hGPV,hPV⟩ :=
    exists_inverse_chart_neighborhood hP3 hG3 hGzero (hchart 0 hzero).1
      (δ := 1) zero_lt_one
  let G : X → E := fun x => G₀ (j x)
  let P : E → X := fun y => j.symm (P₀ y)
  have hG : ContDiff ℝ ∞ G := hG₀.comp j.contDiff
  have hP : ContDiff ℝ ∞ P := j.symm.contDiff.comp hP₀
  refine ⟨c,G,P,hc,hG,hP,?_,?_,?_,V,hV,haV,?_,?_⟩
  · simpa only [G,map_zero] using hGzero
  · simp only [P,hPa,map_zero]
  · intro x hx
    have hx' : j x ∈ closedBall (0 : E) 2 := by
      have hnorm : ‖x‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hx
      simpa only [mem_closedBall,dist_zero_right,j.norm_map] using
        (show ‖x‖ ≤ (2 : ℝ) by linarith)
    obtain ⟨hleft,hlevel⟩ := hchart (j x) hx'
    have hright := chart_local_left_inverse
      (hP₀.differentiable (by simp) (G₀ (j x))) hG3 hleft
    refine ⟨?_,?_,?_⟩
    · have hh := hleft.comp_tendsto (j.continuous.tendsto x)
      filter_upwards [hh] with y hy
      change j.symm (P₀ (G₀ (j y))) = y
      change P₀ (G₀ (j y)) = j y at hy
      rw [hy,j.symm_apply_apply]
    · filter_upwards [hright] with y hy
      change G₀ (j (j.symm (P₀ y))) = y
      rw [j.apply_symm_apply]
      exact hy
    · simpa only [G,hra,sub_zero,j.symm_apply_apply] using hlevel
  · intro y hy
    change G₀ (j (j.symm (P₀ y))) = y
    rw [j.apply_symm_apply]
    exact hGPV y hy
  · intro y hy
    have hp := hPV hy
    simpa only [P,mem_ball,dist_zero_right,j.symm.norm_map] using hp

end OAI.Analysis.PDE.Elliptic
