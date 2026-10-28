import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniformLinear

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance interiorJetFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance interiorJetFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance interiorJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance interiorJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem jet_bounds_on_ball_of_hessian_holder
    (v : E → ℝ) (hv : ContDiff ℝ 2 v) {α N : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hN : 0 ≤ N)
    (h0 : ∀ x ∈ closedBall (0:E) 2, ‖v x‖ ≤ N)
    (h1 : ∀ x ∈ closedBall (0:E) 2, ‖fderiv ℝ v x‖ ≤ N)
    (h2 : ∀ x ∈ closedBall (0:E) 2, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ N)
    (hH : ∀ x ∈ closedBall (0:E) 2, ∀ y ∈ closedBall (0:E) 2,
      ‖fderiv ℝ (fderiv ℝ v) x-fderiv ℝ (fderiv ℝ v) y‖ ≤ N*‖x-y‖^α) :
    C2JetHolderBoundsOn v (closedBall 0 2) α (6*N) := by
  have hscale x (hx : x ∈ closedBall (0:E) 2) y (hy : y ∈ closedBall (0:E) 2) :
      ‖x-y‖ ≤ 5*‖x-y‖^α := by
    have hx' : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hy' : ‖y‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hy
    have hd4 : ‖x-y‖ ≤ 4 := (norm_sub_le x y).trans (by linarith)
    simpa only [show (1:ℝ)+4=5 by norm_num] using
      le_bounded_rpow (norm_nonneg _) (by norm_num : (0:ℝ)≤4) hd4 hα hα1
  have hN6 : N ≤ 6*N := by linarith
  refine ⟨fun x hx ↦ (h0 x hx).trans hN6,fun x hx ↦ (h1 x hx).trans hN6,
    fun x hx ↦ (h2 x hx).trans hN6,?_,?_,?_⟩
  · intro x hx y hy
    have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hv.differentiable (by norm_num) z) h1 (convex_closedBall 0 2) hy hx
    have hs := mul_le_mul_of_nonneg_left (hscale x hx y hy) hN
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    nlinarith
  · intro x hx y hy
    have hb := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z)
      h2 (convex_closedBall 0 2) hy hx
    have hs := mul_le_mul_of_nonneg_left (hscale x hx y hy) hN
    have hp := Real.rpow_nonneg (norm_nonneg (x-y)) α
    nlinarith
  · intro x hx y hy
    exact (hH x hx y hy).trans (mul_le_mul_of_nonneg_right hN6
      (Real.rpow_nonneg (norm_nonneg _) _))

/-- Exact closed-domain jets control normalized affine jets uniformly
in the center and linear map. The image assumption is purely local. -/
theorem stored_jet_affine_uniform
    {Ω Kset : Set E} {hΩK : Ω ⊆ Kset} {α P : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hP : 0 ≤ P)
    (u : E → ℝ) (hu : ContDiff ℝ 2 u) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (hU0 : ∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x)
    (hU1 : ∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x)
    (hU2 : ∀ x : Kset, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x)
    (A : E →L[ℝ] E) (b : E) (hA : ‖A‖ ≤ P)
    (himage : MapsTo (fun z ↦ b+A z) (closedBall 0 2) Kset) :
    C2JetHolderBoundsOn (fun z ↦ u (b+A z)) (closedBall 0 2) α
      (6*(affineJetConstant P α*‖U‖)) := by
  obtain ⟨hQ,hq0,hq1,hq2,_,_,hqa2⟩ := affineJetConstant_bounds (α := α) hP
  have hA2 : ‖A‖^2 ≤ P^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hN := norm_nonneg U
  have h0 x (hx : x ∈ closedBall (0:E) 2) : ‖u (b+A x)‖ ≤ ‖U‖ := by
    rw [← hU0 ⟨b+A x,himage hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.value U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_value_le U)
  have h1 x (hx : x ∈ closedBall (0:E) 2) : ‖fderiv ℝ u (b+A x)‖ ≤ ‖U‖ := by
    rw [← hU1 ⟨b+A x,himage hx⟩]
    exact ((OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U).norm_coe_le_norm _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_firstDerivative_le U)
  have h2 x (hx : x ∈ closedBall (0:E) 2) : ‖fderiv ℝ (fderiv ℝ u) (b+A x)‖ ≤ ‖U‖ := by
    rw [← hU2 ⟨b+A x,himage hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (OAI.Analysis.Normed.Function.Holder.C2Holder.hessianCLM U) _).trans (OAI.Analysis.Normed.Function.Holder.C2Holder.norm_hessianCLM_apply_le U)
  have hH x (hx : x ∈ closedBall (0:E) 2) y (hy : y ∈ closedBall (0:E) 2) :
      ‖fderiv ℝ (fderiv ℝ u) (b+A x)-fderiv ℝ (fderiv ℝ u) (b+A y)‖ ≤
        ‖U‖*‖(b+A x)-(b+A y)‖^α := by
    rw [← hU2 ⟨b+A x,himage hx⟩,← hU2 ⟨b+A y,himage hy⟩]
    simpa only [Subtype.dist_eq,dist_eq_norm] using
      OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder U ⟨b+A x,himage hx⟩ ⟨b+A y,himage hy⟩
  apply jet_bounds_on_ball_of_hessian_holder (fun z ↦ u (b+A z))
    (hu.comp (contDiff_const.add A.contDiff))
    hα hα1 (mul_nonneg hQ.le hN)
  · intro x hx
    apply (h0 x hx).trans
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hq0 hN
  · intro x hx
    rw [localization_affine_first u hu A]
    calc
      _ ≤ ‖fderiv ℝ u (b+A x)‖*‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U‖*P := mul_le_mul (h1 x hx) hA (norm_nonneg _) hN
      _ = P*‖U‖ := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hq1 hN
  · intro x hx
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) (b+A x)‖*‖A‖^2 := localization_affine_second_norm u hu A b x
      _ ≤ ‖U‖*P^2 := mul_le_mul (h2 x hx) hA2 (sq_nonneg _) hN
      _ = P^2*‖U‖ := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hq2 hN
  · intro x hx y hy
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) (b+A x)-fderiv ℝ (fderiv ℝ u) (b+A y)‖*‖A‖^2 :=
        localization_affine_second_sub_norm u hu A b x y
      _ ≤ (‖U‖*‖(b+A x)-(b+A y)‖^α)*P^2 := mul_le_mul (hH x hx y hy) hA2
        (sq_nonneg _) (mul_nonneg hN (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ (‖U‖*(P^α*‖x-y‖^α))*P^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (localization_affine_rpow A b x y hP hA hα) hN) (sq_nonneg _)
      _ = (P^α*P^2*‖U‖)*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqa2 hN)
        (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Dirichlet
