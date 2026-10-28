import OAI.Analysis.PDE.Elliptic.Boundary.ContinuousJet
import OAI.Analysis.Normed.Function.Holder.Banach.Construct
import Mathlib.Analysis.Calculus.MeanValue

/-! The first and second stored jets are genuinely Hölder on a closed
half-chart.  The first-jet bound is derived from the second jet by the
mean-value theorem up to the boundary, not assumed as additional data. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K S : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance chartJetFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance chartJetFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance chartJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance chartJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

theorem norm_secondDerivative_le (U : C2Holder (F := F) hΩK α) :
    ‖C2Holder.secondDerivative U‖ ≤ ‖U‖ :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.value_norm_le _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem hasFDerivWithinAt_chart_first (U : C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {x : E} (hx : x ∈ closure S) :
    HasFDerivWithinAt (fun y => boundedZeroExtension (C2Holder.firstDerivative U) (G y))
      ((boundedZeroExtension (C2Holder.secondDerivative U) (G x)).comp (fderiv ℝ G x))
      (closure S) x := by
  apply OAI.Analysis.PDE.Elliptic.continuous_jet_hasFDerivWithinAt hS hconv
    ((continuousOn_boundedZeroExtension (C2Holder.firstDerivative U)).comp
      hG.continuous.continuousOn hGK)
    (D := fun y => (boundedZeroExtension (C2Holder.secondDerivative U) (G y)).comp (fderiv ℝ G y))
  · exact ((continuousOn_boundedZeroExtension (C2Holder.secondDerivative U)).comp
      hG.continuous.continuousOn hGK).clm_comp (hG.continuous_fderiv one_ne_zero).continuousOn
  · intro y hy
    exact (U.hasFDerivAt_first_extension (hGΩ hy)).comp y
      (hG.differentiable one_ne_zero y).hasFDerivAt
  · exact hx

theorem chart_first_lipschitz (U : C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (_ : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    {x y : E} (hx : x ∈ closure S) (hy : y ∈ closure S) :
    ‖C2Holder.firstDerivative U ⟨G x, hGK hx⟩ - C2Holder.firstDerivative U ⟨G y, hGK hy⟩‖ ≤
      L * ‖U‖ * ‖x-y‖ := by
  have hb : ∀ z ∈ closure S,
      ‖(boundedZeroExtension (C2Holder.secondDerivative U) (G z)).comp (fderiv ℝ G z)‖ ≤ L * ‖U‖ := by
    intro z hz
    rw [boundedZeroExtension_apply _ (hGK hz)]
    calc
      _ ≤ ‖C2Holder.secondDerivative U ⟨G z, hGK hz⟩‖ * ‖fderiv ℝ G z‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U‖ * L := mul_le_mul
        (((C2Holder.secondDerivative U).norm_coe_le_norm _).trans U.norm_secondDerivative_le)
        (hDG z hz) (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hh := hconv.closure.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => U.hasFDerivWithinAt_chart_first hS hconv hG hGK hGΩ hz) hb hy hx
  simpa only [boundedZeroExtension_apply _ (hGK hx),
    boundedZeroExtension_apply _ (hGK hy)] using hh

/-- The original (unpulled-back) first jet has a uniform C^α representative
on a closed chart, with no boundary differentiability assumption. -/
theorem exists_chart_first_holder (U : C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {L : ℝ} (hL : 0 ≤ L) (hDG : ∀ x ∈ closure S, ‖fderiv ℝ G x‖ ≤ L)
    (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1) :
    ∃ D : HolderMap (closure S) (E →L[ℝ] F) α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = C2Holder.firstDerivative U ⟨G x, hGK x.property⟩) ∧
      ‖D‖ ≤ max 1 L * ‖U‖ := by
  let f : closure S →ᵇ (E →L[ℝ] F) :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => C2Holder.firstDerivative U ⟨G x, hGK x.property⟩)
      ((C2Holder.firstDerivative U).continuous.comp
        ((hG.continuous.comp continuous_subtype_val).subtype_mk (fun x => hGK x.property)))
      ‖U‖ (fun x => ((C2Holder.firstDerivative U).norm_coe_le_norm _).trans U.norm_firstDerivative_le)
  have hf : ∀ x y : closure S, ‖f x-f y‖ ≤ (L*‖U‖)*(dist x y)^α := by
    intro x y
    have hd : ‖(x:E)-(y:E)‖ ≤ ‖(x:E)-(y:E)‖^α :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) (hdiam _ x.property _ y.property) hα1
    exact (U.chart_first_lipschitz hS hconv hG hGK hGΩ hL hDG x.property y.property).trans
      (by simpa only [Subtype.dist_eq, dist_eq_norm] using
        mul_le_mul_of_nonneg_left hd (show 0 ≤ L*‖U‖ by positivity))
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα f hf, fun x => rfl, ?_⟩
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα f (by positivity) hf).trans
  have hfn : ‖f‖ ≤ ‖U‖ := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg U) _
  exact (max_le_max hfn le_rfl).trans_eq (by rw [max_mul_of_nonneg _ _ (norm_nonneg U), one_mul])

/-- The existing Hölder second jet remains Hölder after the fixed chart,
with precisely the expected L^α dependence. -/
theorem exists_chart_second_holder (U : C2Holder (F := F) hΩK α)
    {G : E → E} (hG : Continuous G) (hGK : MapsTo G (closure S) K)
    {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖G x-G y‖ ≤ L*‖x-y‖)
    (hα : 0 ≤ α) :
    ∃ H : HolderMap (closure S) (E →L[ℝ] E →L[ℝ] F) α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = C2Holder.secondDerivative U ⟨G x, hGK x.property⟩) ∧
      ‖H‖ ≤ max 1 (L^α) * ‖U‖ := by
  let f : closure S →ᵇ (E →L[ℝ] E →L[ℝ] F) :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => C2Holder.secondDerivative U ⟨G x, hGK x.property⟩)
      ((C2Holder.secondDerivative U).continuous.comp
        ((hG.comp continuous_subtype_val).subtype_mk (fun x => hGK x.property)))
      ‖U‖ (fun x => ((C2Holder.secondDerivative U).norm_coe_le_norm _).trans U.norm_secondDerivative_le)
  have hf : ∀ x y : closure S, ‖f x-f y‖ ≤ (L^α*‖U‖)*(dist x y)^α := by
    intro x y
    have hh := U.secondDerivative_holder ⟨G x, hGK x.property⟩ ⟨G y, hGK y.property⟩
    calc
      _ ≤ ‖U‖ * ‖G x-G y‖^α := by
        change ‖C2Holder.secondDerivative U _ - C2Holder.secondDerivative U _‖ ≤ _
        simpa only [Subtype.dist_eq, dist_eq_norm] using hh
      _ ≤ ‖U‖ * (L*‖(x:E)-(y:E)‖)^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) (hLip _ x.property _ y.property) hα) (norm_nonneg _)
      _ = _ := by rw [Real.mul_rpow hL (norm_nonneg _), Subtype.dist_eq, dist_eq_norm]; ring
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα f hf, fun x => rfl, ?_⟩
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα f (by positivity) hf).trans
  have hfn : ‖f‖ ≤ ‖U‖ := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (norm_nonneg U) _
  exact (max_le_max hfn le_rfl).trans_eq (by rw [max_mul_of_nonneg _ _ (norm_nonneg U), one_mul])

end OAI.Analysis.Normed.Function.Holder.C2Holder
