import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniformLinear
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniformCutoff

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance uniformChartFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformChartFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformChartSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformChartSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem normalized_linear_mapsTo_halfball (k : Fin m) (L : E →L[ℝ] E)
    {r K R : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K) (hL : ‖L‖ ≤ K)
    (hrK : r*K < R/2) (hp : MapsTo L {x | 0 ≤ x k} {x | 0 ≤ x k}) :
    MapsTo (fun z ↦ L (r • z)) ({x | 0 ≤ x k} ∩ closedBall 0 2)
      ({x | 0 ≤ x k} ∩ closedBall 0 R) := by
  intro x hx
  constructor
  · apply hp
    change 0 ≤ (r • x) k
    simp only [PiLp.smul_apply,smul_eq_mul]
    exact mul_nonneg hr hx.1
  · have hxnorm : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx.2
    rw [mem_closedBall,dist_zero_right]
    calc
      _ ≤ ‖L‖*‖r • x‖ := L.le_opNorm _
      _ = ‖L‖*(r*‖x‖) := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr]
      _ ≤ K*(r*2) := mul_le_mul hL (mul_le_mul_of_nonneg_left hxnorm hr)
        (mul_nonneg hr (norm_nonneg _)) hK
      _ ≤ R := by nlinarith

/-- Uniform localization for every bounded halfspace-preserving linear
change of variables. The constant precedes the linear map and solution. -/
theorem exists_uniform_halfspace_chart_hessian_bound
    (k : Fin m) (G : E → E) (hG : ContDiff ℝ 3 G)
    {R r K : ℝ} (_ : 0 < R) (hr : 0 < r) (hK : 0 ≤ K) (hrK : r*K < R/2)
    {Ω Kset : Set E} (himage : MapsTo G ({x | 0 ≤ x k} ∩ closedBall 0 R) Kset)
    {hΩK : Ω ⊆ Kset} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : E →L[ℝ] E, ‖L‖ ≤ K →
      MapsTo L {x | 0 ≤ x k} {x | 0 ≤ x k} →
      ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x, 0 ≤ x k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) x‖ ≤ C*‖U‖) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  let S : Set E := {x | 0 ≤ x k} ∩ closedBall 0 R
  have hHc : IsClosed ({x : E | 0 ≤ x k}) := isClosed_le continuous_const (by fun_prop)
  have hHv : Convex ℝ ({x : E | 0 ≤ x k}) := by
    intro x hx y hy a b ha hb _
    change 0 ≤ (a • x+b • y) k
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have hSc : IsCompact S := (isCompact_closedBall (0 : E) R).inter_left hHc
  have hSv : Convex ℝ S := hHv.inter (convex_closedBall 0 R)
  obtain ⟨B,hB,hGB⟩ := exists_chart_jet_holder_bound G hG hSc hSv himage
    (hΩK := hΩK) hα hα1
  obtain ⟨D,hD,hcut⟩ := exists_halfspace_radial_cutoff_jet_bound k hα hα1
  let P := r*K
  have hP : 0 ≤ P := mul_nonneg hr.le hK
  let Q := affineJetConstant P α
  have hQ : 0 < Q := (affineJetConstant_bounds (α := α) hP).1
  refine ⟨D*(Q*B),by positivity,?_⟩
  intro L hL hp u hu U hU₀ hU₁ hU₂
  let A : E →L[ℝ] E := r • L
  have hA : ‖A‖ ≤ P := by
    dsimp [A,P]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hL hr.le
  have hmap : MapsTo (fun z ↦ (0 : E)+A z) ({x | 0 ≤ x k} ∩ closedBall 0 2) S := by
    simpa only [zero_add,A,smul_apply,map_smul] using
      normalized_linear_mapsTo_halfball k L hr.le hK hL hrK hp
  let v := fun z ↦ u (G z)
  have hv : ContDiff ℝ 2 v := hu.comp (hG.of_le (by norm_num))
  have hbase : C2JetHolderBoundsOn v S α (B*‖U‖) := hGB u hu U hU₀ hU₁ hU₂
  have hpull := hbase.affine_uniform hv (mul_nonneg hB.le (norm_nonneg U)) hP hα A 0 hA hmap
  have hvc : ContDiff ℝ 2 (fun z ↦ v ((0:E)+A z)) := hv.comp (contDiff_const.add A.contDiff)
  have hh := hcut (fun z ↦ v ((0:E)+A z)) hvc (Q*(B*‖U‖)) (by positivity) hpull
  simpa only [v,zero_add,A,smul_apply,map_smul,mul_assoc] using hh

/-- Coordinate-preserving equivalences used in boundary normalization
are covered by the same uniform constant; no inverse norm is required. -/
theorem exists_uniform_halfspace_equiv_chart_hessian_bound
    (k : Fin m) (G : E → E) (hG : ContDiff ℝ 3 G)
    {R r K : ℝ} (hR : 0 < R) (hr : 0 < r) (hK : 0 ≤ K) (hrK : r*K < R/2)
    {Ω Kset : Set E} (himage : MapsTo G ({x | 0 ≤ x k} ∩ closedBall 0 R) Kset)
    {hΩK : Ω ⊆ Kset} {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : E ≃L[ℝ] E, ‖L.toContinuousLinearMap‖ ≤ K →
      (∃ c : ℝ, 0 < c ∧ ∀ z : E, (L z) k = c*z k) →
      ∀ u : E → ℝ, ContDiff ℝ 2 u → ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      (∀ x, 0 ≤ x k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) x‖ ≤ C*‖U‖) ∧
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) x-
          fderiv ℝ (fderiv ℝ (fun z ↦ OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z*u (G (L (r • z))))) y‖ ≤ C*‖U‖*‖x-y‖^α) := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_halfspace_chart_hessian_bound k G hG hR hr hK hrK
    himage (hΩK := hΩK) hα hα1
  refine ⟨C,hC,?_⟩
  intro L hL ⟨c,hc,he⟩
  apply hbound L.toContinuousLinearMap hL
  intro z hz
  change 0 ≤ (L z) k
  rw [he]
  exact mul_nonneg hc.le hz

end OAI.Analysis.PDE.Dirichlet
