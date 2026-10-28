import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Source
import OAI.Analysis.PDE.Elliptic.Boundary.ChainRule

/-! The drift in a differentiated curved-chart equation is controlled by
the original C²,α jets. It does not cost a third derivative. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {X E : Type*} [MetricSpace X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {α : ℝ}

local instance chartDriftSourceFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance chartDriftSourceFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance chartDriftSourceSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartDriftSourceSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance chartDriftSourceEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance chartDriftSourceEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance chartDriftSourceEndSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance chartDriftSourceEndSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def holderChartDirectionalDrift (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (e : E) : OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα H (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα J V)) (holderEvaluate J e) +
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D (holderEvaluate (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα K V) e)

omit [FiniteDimensional ℝ E] in
theorem value_holderChartDirectionalDrift (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) (e : E) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderChartDirectionalDrift hα D H J K V e) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (OAI.Analysis.Normed.Function.Holder.HolderMap.value V x)) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x e) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x (OAI.Analysis.Normed.Function.Holder.HolderMap.value V x) e) := rfl

omit [FiniteDimensional ℝ E] in
theorem holderChartDirectionalDrift_norm_le (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E) α) (K : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {e : E} (he : ‖e‖ ≤ 1) :
    ‖holderChartDirectionalDrift hα D H J K V e‖ ≤
      8 * ‖H‖ * ‖J‖^2 * ‖V‖ + 4 * ‖D‖ * ‖K‖ * ‖V‖ := by
  unfold holderChartDirectionalDrift
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    calc
      _ ≤ 2 * (2 * ‖H‖ * (2 * ‖J‖ * ‖V‖)) * ‖J‖ := by
        gcongr
        · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
            (mul_le_mul_of_nonneg_left (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα J V) (by positivity))
        · exact holderEvaluate_norm_le J he
      _ = _ := by ring
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    calc
      _ ≤ 2 * ‖D‖ * (2 * ‖K‖ * ‖V‖) := by
        gcongr
        exact (holderEvaluate_norm_le _ he).trans (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα K V)
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
theorem chart_directional_drift_formula {u : E → ℝ} {G : E → E} {x : E}
    (hu : ContDiffAt ℝ 2 u (G x)) (hG : ContDiffAt ℝ 2 G x) (e v : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => u (G y)) z e) x v =
      fderiv ℝ (fderiv ℝ u) (G x) (fderiv ℝ G x v) (fderiv ℝ G x e) +
      fderiv ℝ u (G x) (fderiv ℝ (fderiv ℝ G) x v e) := by
  have hh : ContDiffAt ℝ 2 (fun y => u (G y)) x := hu.comp x hG
  have hd := ((hh.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const e x)
  rw [hd.fderiv]
  simpa using
    second_fderiv_comp hu hG v e

omit [FiniteDimensional ℝ E] in
theorem exists_chart_directional_drift_holder_interior {Ω K₀ S : Set E} {hΩK : Ω ⊆ K₀}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hΩ : IsOpen Ω) (hS : IsOpen S) (hconv : Convex ℝ S)
    {G : E → E} (hG : ContDiff ℝ 2 G)
    (hGK : MapsTo G (closure S) K₀) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) E α) (v : E → E)
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x)
    (hK : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x)
    (hV : ∀ x, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V ⟨x, subset_closure hx⟩ = v x)
    {e : E} (he : ‖e‖ ≤ 1) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x : E, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩ =
        fderiv ℝ (fun z => fderiv ℝ (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y)) z e) x (v x)) ∧
      ‖R‖ ≤ 8 * (max 1 (L^α) * ‖U‖) * ‖J‖^2 * ‖V‖ +
        4 * (max 1 L * ‖U‖) * ‖K‖ * ‖V‖ := by
  obtain ⟨D, hD, hnD⟩ := U.exists_chart_first_holder hS hconv (hG.of_le (by norm_num))
    hGK hGΩ hL hDG hα hα1 hdiam
  have hLip : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖G x-G y‖ ≤ L*‖x-y‖ := by
    intro x hx y hy
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG.differentiable (by norm_num) z) hDG hconv.closure hy hx
  obtain ⟨H, hH, hnH⟩ := U.exists_chart_second_holder hG.continuous hGK hL hLip hα
  refine ⟨holderChartDirectionalDrift hα D H J K V e, ?_, ?_⟩
  · intro x hx
    have hu := (OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ U).contDiffAt (hΩ.mem_nhds (hGΩ hx))
    rw [value_holderChartDirectionalDrift, chart_directional_drift_formula hu hG.contDiffAt]
    have hj := U.genuine_derivatives hΩ (hGΩ hx)
    simp only [hD, hH, hJ, hK, hV x hx, hj.1, hj.2]
  · apply (holderChartDirectionalDrift_norm_le hα D H J K V he).trans
    gcongr

omit [FiniteDimensional ℝ E] in
theorem exists_chart_directional_drift_holder {Ω K₀ S : Set E} {hΩK : Ω ⊆ K₀}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (hΩ : IsOpen Ω) (hS : IsOpen S) (hconv : Convex ℝ S)
    {G : E → E} (hG : ContDiff ℝ 2 G)
    (hGK : MapsTo G (closure S) K₀) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) (E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) E α) (v : E → E)
    (hJ : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x)
    (hK : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x)
    (hV : ∀ x : closure S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = v x)
    {e : E} (he : ‖e‖ ≤ 1) :
    ∃ R : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α,
      (∀ x : E, ∀ hx : x ∈ S, OAI.Analysis.Normed.Function.Holder.HolderMap.value R ⟨x, subset_closure hx⟩ =
        fderiv ℝ (fun z => fderiv ℝ (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y)) z e) x (v x)) ∧
      ‖R‖ ≤ 8 * (max 1 (L^α) * ‖U‖) * ‖J‖^2 * ‖V‖ +
        4 * (max 1 L * ‖U‖) * ‖K‖ * ‖V‖ :=
  exists_chart_directional_drift_holder_interior U hΩ hS hconv hG hGK hGΩ hL hDG
    hα hα1 hdiam J K V v hJ hK (fun x hx => hV ⟨x, subset_closure hx⟩) he

end OAI.Analysis.PDE.Elliptic
