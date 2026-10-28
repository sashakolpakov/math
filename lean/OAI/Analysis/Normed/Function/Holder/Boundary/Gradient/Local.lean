import OAI.Analysis.Normed.Function.Holder.Boundary.ChartJets
import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJetBounds

/-! Uniform first-jet Hölder control on a physical chart. Only the stored
second-order norm is used; no global differentiable representative is assumed. -/

noncomputable section
open Set Metric
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

open OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance gradientLocalFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance gradientLocalFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance gradientLocalSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance gradientLocalSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem chart_first_jet_holder_bound
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hS : IsOpen S) (hconv : Convex ℝ S)
    (hcompact : IsCompact (closure S)) {G P : E → E}
    (hG : ContDiff ℝ 1 G) (hP : ContDiff ℝ 1 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {a : E} {ρ α : ℝ} (hρ : ρ ≤ 1/2) (hα1 : α ≤ 1)
    (hPK : MapsTo P (closedBall a ρ ∩ K) (closure S))
    (hleft : ∀ x ∈ closedBall a ρ ∩ K, G (P x) = x) :
    ∃ C > 0, ∀ U : C2Holder (F := ℝ) hΩK α,
      ∀ x ∈ closedBall a ρ, x ∈ K → ∀ y ∈ closedBall a ρ, y ∈ K →
      ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
        C*‖U‖*dist x y^α := by
  obtain ⟨L₀,hL₀⟩ := hcompact.exists_bound_of_continuousOn (hG.continuous_fderiv one_ne_zero).continuousOn
  let L := max 1 L₀
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDG (x) (hx : x ∈ closure S) : ‖fderiv ℝ G x‖ ≤ L :=
    (hL₀ x hx).trans (le_max_right _ _)
  obtain ⟨M,hM,_,hLip⟩ := OAI.Analysis.PDE.Dirichlet.smooth_jet_compact_holder_bound P hP (isCompact_closedBall a ρ)
    (by norm_num : (0 : ℝ) ≤ 1) le_rfl
  refine ⟨L*M, mul_pos hL hM, ?_⟩
  intro U x hx hxK y hy hyK
  have hxP := hPK ⟨hx,hxK⟩
  have hyP := hPK ⟨hy,hyK⟩
  have hh := U.chart_first_lipschitz hS hconv hG hGK hGΩ hL.le hDG hxP hyP
  have hfirst :
      ‖boundedZeroExtension (C2Holder.firstDerivative U) x-boundedZeroExtension (C2Holder.firstDerivative U) y‖ ≤
        L*‖U‖*‖P x-P y‖ := by
    rw [boundedZeroExtension_apply _ hxK, boundedZeroExtension_apply _ hyK]
    simpa only [hleft x ⟨hx,hxK⟩, hleft y ⟨hy,hyK⟩] using hh
  have hp : ‖P x-P y‖ ≤ M*dist x y := by
    simpa only [Real.rpow_one] using hLip x hx y hy
  have hdist : dist x y ≤ 1 := by
    have hxy := dist_triangle x a y
    have hxa : dist x a ≤ ρ := hx
    have hay : dist a y ≤ ρ := by simpa only [mem_closedBall, dist_comm] using hy
    linarith
  have hrpow : dist x y ≤ dist x y^α := Real.self_le_rpow_of_le_one dist_nonneg hdist hα1
  calc
    _ ≤ L*‖U‖*(M*dist x y) := hfirst.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    _ ≤ L*‖U‖*(M*(dist x y^α)) := by gcongr
    _ = _ := by ring

end OAI.Analysis.Normed.Function.Holder.C2Holder
