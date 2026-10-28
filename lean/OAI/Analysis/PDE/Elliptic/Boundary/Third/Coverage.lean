import OAI.Analysis.PDE.Elliptic.Boundary.InverseSubtractedHolder
import OAI.Analysis.PDE.Elliptic.PeriodicChartCoverage

/-! A fixed physical neighborhood for the third-order boundary estimate.
The inverse germ, coverage, and restoration of boundary data are all derived
from the original smooth chart. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I
local instance thirdCoverFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdCoverFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdCoverSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCoverSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCoverThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdCoverThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [DecidableEq I] in
theorem exists_level_chart_coverage {P G : E → E} {a : E}
    {r ℓ : E → ℝ} {c : ℝ} (hc : 0 < c)
    (hP : ContDiff ℝ 3 P) (hG : ContDiff ℝ 3 G) (hG0 : G 0 = a)
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*ℓ z)
    (hra : r a = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R > 0, ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ closedBall a R ⊆ V ∧
      (∀ x ∈ V, G (P x) = x) ∧
      MapsTo P (closedBall a R ∩ {x | r x ≤ 0}) (ball 0 δ ∩ {z | 0 ≤ ℓ z}) := by
  obtain ⟨_, R, hR, V, hV, haV, hRV, hleft, hPV⟩ :=
    exists_inverse_chart_neighborhood hP hG hG0 hinv (lt_min hδ zero_lt_one)
  refine ⟨R, hR, V, hV, haV, hRV, hleft, ?_⟩
  intro x hx
  have hxV := hRV hx.1
  have hsmall := hPV hxV
  have hb : P x ∈ closedBall 0 2 := by
    apply ball_subset_closedBall
    exact ball_subset_ball (by exact (min_le_right δ 1).trans (by norm_num)) hsmall
  have heq : r x = -c*ℓ (P x) := by
    simpa only [hleft x hxV, hra, sub_zero] using hlevel (P x) hb
  refine ⟨ball_subset_ball (min_le_left δ 1) hsmall, ?_⟩
  have hrx : r x ≤ 0 := hx.2
  change 0 ≤ ℓ (P x)
  rw [heq] at hrx
  nlinarith

theorem exists_physical_third_return {P G : E → E} {a : E}
    {r ℓ : E → ℝ} {c : ℝ} (hc : 0 < c) (hr : Continuous r)
    (hP : ContDiff ℝ 4 P) (hG : ContDiff ℝ 4 G) (hG0 : G 0 = a)
    (hinv : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*ℓ z)
    (hra : r a = 0) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α δ : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hδ : 0 < δ) :
    ∃ R > 0, ∃ C > 0, ∀ u : E → ℝ, ContDiff ℝ 3 u →
      ∀ N M : ℝ, 0 ≤ N → 0 ≤ M →
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (fun z => u (G z)-B₀ (G z))
        (ball 0 δ ∩ {z | 0 ≤ ℓ z}) α N →
      (∀ z ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z},
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) z‖ ≤ M) →
      (∀ z ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z}, ∀ w ∈ ball 0 δ ∩ {z | 0 ≤ ℓ z},
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) z-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)-B₀ (G y)))) w‖ ≤
            M*‖z-w‖^α) →
      (∀ x ∈ closedBall a R, r x ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ C*(1+N+M)) ∧
      (∀ x ∈ closedBall a R, r x ≤ 0 → ∀ y ∈ closedBall a R, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤ C*(1+N+M)*‖x-y‖^α) := by
  obtain ⟨R, hR, V, hV, _, hRV, hleft, hmaps⟩ := exists_level_chart_coverage hc
    (hP.of_le (by norm_num)) (hG.of_le (by norm_num)) hG0 hinv hlevel hra hδ
  have hcompact : IsCompact (closedBall a R ∩ {x | r x ≤ 0}) :=
    (isCompact_closedBall a R).inter_right (isClosed_le hr continuous_const)
  obtain ⟨C, hC, hreturn⟩ := exists_inverse_subtracted_third_holder hcompact hP B₀ hB₀ hα hα1
  refine ⟨R, hR, C, hC, ?_⟩
  intro u hu N M hN hM hb hn hh
  have heq (x) (hx : x ∈ closedBall a R ∩ {x | r x ≤ 0}) :
      (fun y => u (G (P y))-B₀ (G (P y))) =ᶠ[𝓝 x] (fun y => u y-B₀ y) := by
    filter_upwards [hV.mem_nhds (hRV hx.1)] with y hy
    rw [hleft y hy]
  obtain ⟨T, hT, hTn⟩ := hreturn _ hmaps _ u
    ((hu.sub (hB₀.of_le (by norm_num))).comp (hG.of_le (by norm_num)))
    hu heq N M hN hM hb hn hh
  constructor
  · intro x hx hrx
    rw [← hT ⟨x, hx, hrx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le T _).trans hTn
  · intro x hx hrx y hy hry
    rw [← hT ⟨x, hx, hrx⟩, ← hT ⟨y, hy, hry⟩]
    have hbound := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le T ⟨x, hx, hrx⟩ ⟨y, hy, hry⟩
    exact hbound.trans (mul_le_mul_of_nonneg_right hTn (by positivity))

end OAI.Analysis.PDE.Elliptic
