import OAI.Analysis.Normed.Function.Holder.Boundary.Gradient.Local
import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalSmoothChart
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatchClosure
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Coverage

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Elliptic

variable {I : Type*} [Fintype I] [DecidableEq I] {m : ℕ}
local notation "E" => EuclideanSpace ℝ I
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance gradientBoundaryFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientBoundaryFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

omit [DecidableEq I] in
theorem boundary_first_jet_holder_bound
    (e : X ≃ₗᵢ[ℝ] E) (k : Fin m) {r : E → ℝ}
    (hr : ContDiff ℝ ∞ r)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {a : E} (ha : r a = 0) (hreg : fderiv ℝ r a ≠ 0)
    {α : ℝ} (hα1 : α ≤ 1) :
    ∃ ρ > 0, ∃ C > 0, ∀ U : C2Holder (F := ℝ) hΩK α,
      ∀ x ∈ closedBall a ρ, r x ≤ 0 → ∀ y ∈ closedBall a ρ, r y ≤ 0 →
      ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
        C*‖U‖*dist x y^α := by
  obtain ⟨c,G,P,hc,hG,hP,hG0,hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_physical_smooth_coordinate_chart e k hr a hreg
  let S := OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e k
  have hclosed (z : E) (hz : z ∈ closure S) :
      e.symm z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2) := by
    simpa only [S, OAI.Analysis.PDE.Elliptic.closure_positiveIsometryHalfPatch, mem_preimage] using hz
  have hball (z : E) (hz : z ∈ closure S) : z ∈ closedBall 0 2 := by
    have hn : ‖z‖ ≤ (1/2 : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using (hclosed z hz).1
    simpa only [mem_closedBall, dist_zero_right] using hn.trans (by norm_num)
  have hGK : MapsTo G (closure S) {x | r x ≤ 0} := by
    intro z hz
    have h := (hchart z (hball z hz)).2
    have hp : 0 ≤ e.symm z k := (hclosed z hz).2
    change r (G z) ≤ 0
    rw [ha, sub_zero] at h
    nlinarith
  have hGΩ : MapsTo G S {x | r x < 0} := by
    intro z hz
    have hp : 0 < e.symm z k := hz.2
    have h := (hchart z (hball z (subset_closure hz))).2
    change r (G z) < 0
    rw [ha, sub_zero] at h
    nlinarith
  obtain ⟨R,hR,V,_,_,hRV,hleft,hPV⟩ := OAI.Analysis.PDE.Elliptic.exists_level_chart_coverage hc
    (hP.of_le (by simp)) (hG.of_le (by simp)) hG0
    (hchart 0 (mem_closedBall_self (by norm_num))).1
    (fun z hz => (hchart z hz).2) ha (by norm_num : (0 : ℝ) < 1/4)
  let ρ := min R (1/2)
  have hρ : 0 < ρ := lt_min hR (by norm_num)
  have hsmall : closedBall a ρ ⊆ closedBall a R := closedBall_subset_closedBall (min_le_left _ _)
  have hmaps : MapsTo P (closedBall a ρ ∩ {x | r x ≤ 0}) (closure S) := by
    intro x hx
    have hp := hPV ⟨hsmall hx.1,hx.2⟩
    change P x ∈ closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e k)
    rw [OAI.Analysis.PDE.Elliptic.closure_positiveIsometryHalfPatch]
    change e.symm (P x) ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2)
    refine ⟨?_,hp.2⟩
    have hn : ‖P x‖ < (1/4 : ℝ) := by simpa only [mem_ball, dist_zero_right] using hp.1
    simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using hn.le.trans (by norm_num)
  obtain ⟨C,hC,hbound⟩ := C2Holder.chart_first_jet_holder_bound hΩK
    (OAI.Analysis.PDE.Elliptic.isOpen_positiveIsometryHalfPatch e k) (OAI.Analysis.PDE.Elliptic.convex_positiveIsometryHalfPatch e k)
    (OAI.Analysis.PDE.Elliptic.isCompact_closure_positiveIsometryHalfPatch e k)
    (hG.of_le (by simp)) (hP.of_le (by simp)) hGK hGΩ
    (min_le_right R (1/2)) hα1 hmaps
    (fun x hx => hleft x (hRV (hsmall hx.1)))
  exact ⟨ρ,hρ,C,hC,hbound⟩

end OAI.Analysis.Normed.Function.Holder.C2Holder
