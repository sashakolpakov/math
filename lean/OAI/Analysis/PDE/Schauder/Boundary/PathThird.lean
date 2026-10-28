import OAI.Analysis.PDE.Elliptic.Boundary.Third.Absorption
import OAI.Analysis.PDE.Elliptic.Boundary.PhysicalSmoothChart
import OAI.Analysis.PDE.Elliptic.Boundary.HalfPatchClosure
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.PathSolution
import OAI.Analysis.PDE.Schauder.Dirichlet.PathThirdGlobal

/-! The boundary third-order estimate for actual nonlinear density-path
solutions. Its chart, forcing, lower jets, and original third-jet field
are all constructed from the fixed data. -/

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Elliptic

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => EuclideanSpace ℝ (Fin (n*4))
local instance boundaryPathThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundaryPathThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

private theorem physical_positive_chart_properties (e₀ : X ≃ₗᵢ[ℝ] E) (k : Fin (n*4))
    {r : E → ℝ} {a : E} (hra : r a = 0) {c : ℝ} (hc : 0 < c) (G : E → E)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*(e₀.symm z) k) :
    (closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k) ⊆ closedBall 0 2) ∧
    MapsTo G (closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) {x | r x ≤ 0} ∧
    MapsTo G (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k) {x | r x < 0} ∧
    (∀ x ∈ ball (0 : X) (1/2), x k = 0 → r (G (e₀ x)) = 0) := by
  have hclosed (z : E) (hz : z ∈ closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) :
      e₀.symm z ∈ OAI.Analysis.PDE.Elliptic.closedCoordinateHalfPatch k 0 (1/2) := by
    rw [OAI.Analysis.PDE.Elliptic.closure_positiveIsometryHalfPatch] at hz
    exact hz
  have hball (z : E) (hz : z ∈ closure (OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k)) : z ∈ closedBall 0 2 := by
    have hnz : ‖z‖ ≤ (1/2 : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right, e₀.symm.norm_map] using (hclosed z hz).1
    simpa only [mem_closedBall, dist_zero_right] using hnz.trans (by norm_num)
  refine ⟨fun z hz => hball z hz, ?_, ?_, ?_⟩
  · intro z hz
    have h := hlevel z (hball z hz)
    have hp : 0 ≤ e₀.symm z k := (hclosed z hz).2
    change r (G z) ≤ 0
    rw [hra, sub_zero] at h
    nlinarith
  · intro z hz
    have hp : 0 < e₀.symm z k := hz.2
    have h := hlevel z (hball z (subset_closure hz))
    change r (G z) < 0
    rw [hra, sub_zero] at h
    nlinarith
  · intro x hx hxk
    have hxnorm : ‖x‖ < (1/2 : ℝ) := by simpa only [mem_ball, dist_zero_right] using hx
    have hb : e₀ x ∈ closedBall 0 2 := by
      simpa only [mem_closedBall, dist_zero_right, e₀.norm_map] using
        hxnorm.le.trans (by norm_num : (1/2 : ℝ) ≤ 2)
    simpa only [hra, sub_zero, e₀.symm_apply_apply, hxk, mul_zero] using hlevel (e₀ x) hb

theorem BoundaryThirdPathData.boundary_estimate
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    {d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK} (b : BoundaryThirdPathData d)
    (hn : 3 ≤ n*4) (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) : BoundaryThirdPathEstimate d := by
  intro a hra
  let e₀ : X ≃ₗᵢ[ℝ] E := (OAI.Analysis.PDE.Dirichlet.flattenFourSlots n).symm
  let k : Fin (n*4) := ⟨0, by omega⟩
  obtain ⟨c,G,Q,hc,hG,hQ,hG0,hchart⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_physical_smooth_coordinate_chart e₀ k hr a (hreg a hra)
  let S : Set E := OAI.Analysis.PDE.Elliptic.positiveIsometryHalfPatch e₀ k
  have hSC : IsCompact (closure S) := OAI.Analysis.PDE.Elliptic.isCompact_closure_positiveIsometryHalfPatch e₀ k
  obtain ⟨hball,hGK,hGΩ,hboundary⟩ := physical_positive_chart_properties e₀ k hra hc G
    (fun z hz => (hchart z hz).2)
  obtain ⟨ρ,hρ,hestimate⟩ := OAI.Analysis.PDE.Elliptic.nonlinear_physical_boundary_third_estimate hn e₀ k r hr.continuous a hra
    hΩK (OAI.Analysis.PDE.Elliptic.isOpen_positiveIsometryHalfPatch e₀ k) (OAI.Analysis.PDE.Elliptic.convex_positiveIsometryHalfPatch e₀ k)
    hSC (OAI.Analysis.PDE.Elliptic.diameter_positiveIsometryHalfPatch e₀ k) (OAI.Analysis.PDE.Elliptic.halfPatch_subset_isometry_closure e₀ k)
    (fun x hx hxk => OAI.Analysis.PDE.Elliptic.positive_halfBall_mem_isometry_patch e₀ k hx hxk)
    G Q (hG.of_le (by simp)) (hQ.of_le (by simp)) hG0
    (hchart 0 (mem_closedBall_self (by norm_num))).1 hGK hGΩ
    (fun z hz => (hchart z (hball hz)).1) hc (fun z hz => (hchart z hz).2)
    B₀ hB₀ d.exponent_pos d.exponent_lt_one d.normBound_pos.le b.coefficientBound_nonneg
    b.gradientBound_pos.le b.lower_pos b.upper_nonneg
  refine ⟨ρ,hρ,?_⟩
  intro ε hε
  obtain ⟨D,hD,hbound⟩ := hestimate ε hε
  refine ⟨D,hD,?_⟩
  intro s T hT
  let p := b.toBoundaryLogSolution hr.continuous hB₀ hF₀ hF₁ e₀ k S G hGΩ hboundary s
  have hpu : p.u = fun y => B₀ y+s.u y := rfl
  obtain ⟨hval,hholder⟩ := hbound p T hT
  exact ⟨hval, fun x hx hrx y hy hry => by
    simpa only [hpu, dist_eq_norm] using hholder x hx hrx y hy hry⟩

end OAI.Analysis.PDE.Schauder
