import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.Localization
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Affine

open Set Metric
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.PDE.Schauder

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance uniformLinearFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformLinearFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformLinearSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformLinearSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem localization_affine_first (v : E → ℝ) (hv : ContDiff ℝ 2 v)
    (A : E →L[ℝ] E) (b x : E) :
    fderiv ℝ (fun z ↦ v (b+A z)) x = (fderiv ℝ v (b+A x)).comp A := by
  have ha : HasFDerivAt (fun z ↦ b+A z) A x := by
    simpa only [zero_add] using A.hasFDerivAt.const_add b
  exact ((hv.differentiable (by norm_num) _).hasFDerivAt.comp x ha).fderiv

theorem localization_affine_second_norm (v : E → ℝ) (hv : ContDiff ℝ 2 v)
    (A : E →L[ℝ] E) (b x : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ v (b+A z))) x‖ ≤
      ‖fderiv ℝ (fderiv ℝ v) (b+A x)‖*‖A‖^2 := by
  apply OAI.Analysis.PDE.Schauder.bilinear_norm_le_pullback
  exact OAI.Analysis.PDE.Schauder.second_fderiv_comp_affine v hv A b x

theorem localization_affine_second_sub_norm (v : E → ℝ) (hv : ContDiff ℝ 2 v)
    (A : E →L[ℝ] E) (b x y : E) :
    ‖fderiv ℝ (fderiv ℝ (fun z ↦ v (b+A z))) x-
      fderiv ℝ (fderiv ℝ (fun z ↦ v (b+A z))) y‖ ≤
      ‖fderiv ℝ (fderiv ℝ v) (b+A x)-fderiv ℝ (fderiv ℝ v) (b+A y)‖*‖A‖^2 := by
  apply OAI.Analysis.PDE.Schauder.bilinear_norm_le_pullback
  intro a c
  simp only [sub_apply, OAI.Analysis.PDE.Schauder.second_fderiv_comp_affine v hv A]

def affineJetConstant (P α : ℝ) : ℝ :=
  1+P+P^2+P^α+P^α*P+P^α*P^2

theorem affineJetConstant_bounds {P α : ℝ} (hP : 0 ≤ P) :
    0 < affineJetConstant P α ∧ 1 ≤ affineJetConstant P α ∧
    P ≤ affineJetConstant P α ∧ P^2 ≤ affineJetConstant P α ∧
    P^α ≤ affineJetConstant P α ∧ P^α*P ≤ affineJetConstant P α ∧
    P^α*P^2 ≤ affineJetConstant P α := by
  have hpow := Real.rpow_nonneg hP α
  have hsq := sq_nonneg P
  have h1 := mul_nonneg hpow hP
  have h2 := mul_nonneg hpow hsq
  unfold affineJetConstant
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem localization_affine_rpow (A : E →L[ℝ] E) (b x y : E)
    {P α : ℝ} (hP : 0 ≤ P) (hA : ‖A‖ ≤ P) (hα : 0 ≤ α) :
    ‖(b+A x)-(b+A y)‖^α ≤ P^α*‖x-y‖^α := by
  have he : (b+A x)-(b+A y) = A (x-y) := by rw [map_sub]; abel
  rw [he, ← Real.mul_rpow hP (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) ((A.le_opNorm _).trans
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _))) hα

/-- Bounded affine precomposition preserves all three Hölder jet bounds,
with a constant depending only on the upper bound for the linear part. -/
theorem C2JetHolderBoundsOn.affine_uniform
    {v : E → ℝ} (hv : ContDiff ℝ 2 v) {S T : Set E} {α N P : ℝ}
    (hN : 0 ≤ N) (hP : 0 ≤ P) (hα : 0 ≤ α)
    (hb : C2JetHolderBoundsOn v S α N) (A : E →L[ℝ] E) (b : E)
    (hA : ‖A‖ ≤ P) (himage : MapsTo (fun z ↦ b+A z) T S) :
    C2JetHolderBoundsOn (fun z ↦ v (b+A z)) T α (affineJetConstant P α*N) := by
  obtain ⟨_,hq0,hq1,hq2,hqa,hqa1,hqa2⟩ := affineJetConstant_bounds (α := α) hP
  have hA2 : ‖A‖^2 ≤ P^2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have hd x y := localization_affine_rpow A b x y hP hA hα
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    apply (hb.value _ (himage hx)).trans
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq0 hN)
  · intro x hx
    rw [localization_affine_first v hv A]
    calc
      _ ≤ ‖fderiv ℝ v (b+A x)‖*‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ N*P := mul_le_mul (hb.first _ (himage hx)) hA (norm_nonneg _) hN
      _ = P*N := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hq1 hN
  · intro x hx
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ v) (b+A x)‖*‖A‖^2 := localization_affine_second_norm v hv A b x
      _ ≤ N*P^2 := mul_le_mul (hb.second _ (himage hx)) hA2 (sq_nonneg _) hN
      _ = P^2*N := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hq2 hN
  · intro x hx y hy
    calc
      _ ≤ N*‖(b+A x)-(b+A y)‖^α := hb.value_sub _ (himage hx) _ (himage hy)
      _ ≤ N*(P^α*‖x-y‖^α) := mul_le_mul_of_nonneg_left (hd x y) hN
      _ = (P^α*N)*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqa hN)
        (Real.rpow_nonneg (norm_nonneg _) _)
  · intro x hx y hy
    rw [localization_affine_first v hv A,localization_affine_first v hv A]
    have he : (fderiv ℝ v (b+A x)).comp A-(fderiv ℝ v (b+A y)).comp A =
        (fderiv ℝ v (b+A x)-fderiv ℝ v (b+A y)).comp A := by ext z; rfl
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ v (b+A x)-fderiv ℝ v (b+A y)‖*‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (N*‖(b+A x)-(b+A y)‖^α)*P := mul_le_mul
        (hb.first_sub _ (himage hx) _ (himage hy)) hA (norm_nonneg _)
        (mul_nonneg hN (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ (N*(P^α*‖x-y‖^α))*P := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd x y) hN) hP
      _ = (P^α*P*N)*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqa1 hN)
        (Real.rpow_nonneg (norm_nonneg _) _)
  · intro x hx y hy
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ v) (b+A x)-fderiv ℝ (fderiv ℝ v) (b+A y)‖*‖A‖^2 :=
        localization_affine_second_sub_norm v hv A b x y
      _ ≤ (N*‖(b+A x)-(b+A y)‖^α)*P^2 := mul_le_mul
        (hb.second_sub _ (himage hx) _ (himage hy)) hA2 (sq_nonneg _)
        (mul_nonneg hN (Real.rpow_nonneg (norm_nonneg _) _))
      _ ≤ (N*(P^α*‖x-y‖^α))*P^2 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hd x y) hN) (sq_nonneg _)
      _ = (P^α*P^2*N)*‖x-y‖^α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hqa2 hN)
        (Real.rpow_nonneg (norm_nonneg _) _)

end OAI.Analysis.PDE.Dirichlet
