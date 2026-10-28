import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

universe u v
variable {K : Type v} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition on the left on the Banach space of continuous paths. -/
def superpose (f : E → F) (hf : Continuous f) (u : C(K, E)) : C(K, F) :=
  ⟨fun x => f (u x), hf.comp u.continuous⟩

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem superpose_apply (f : E → F) (hf : Continuous f) (u : C(K,E)) (x : K) :
    superpose f hf u x = f (u x) := rfl

/-- Pointwise application of a continuous family of linear maps. -/
def applyField (A : C(K, E →L[ℝ] F)) : C(K,E) →L[ℝ] C(K,F) :=
  LinearMap.mkContinuous
    ({ toFun := fun u => ⟨fun x => A x (u x), A.continuous.clm_apply u.continuous⟩
       map_add' := by intro u v; ext x; exact map_add (A x) (u x) (v x)
       map_smul' := by intro c u; ext x; exact map_smul (A x) c (u x) } : C(K,E) →ₗ[ℝ] C(K,F))
    ‖A‖ (by
      intro u
      change ‖(⟨fun x => A x (u x), A.continuous.clm_apply u.continuous⟩ : C(K,F))‖ ≤ ‖A‖*‖u‖
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg u))).2
      intro x
      exact (A x).le_opNorm (u x) |>.trans
        (mul_le_mul (A.norm_coe_le_norm x) (u.norm_coe_le_norm x)
          (norm_nonneg _) (norm_nonneg _)))

@[simp] theorem applyField_apply (A : C(K,E →L[ℝ] F)) (u : C(K,E)) (x : K) :
    applyField A u x = A x (u x) := rfl

theorem norm_applyField_le (A : C(K,E →L[ℝ] F)) : ‖applyField A‖ ≤ ‖A‖ := by
  unfold applyField
  apply LinearMap.mkContinuous_norm_le
  exact norm_nonneg A

def applyFieldLinear : C(K,E →L[ℝ] F) →ₗ[ℝ] (C(K,E) →L[ℝ] C(K,F)) where
  toFun A := applyField A
  map_add' A B := by ext u x; rfl
  map_smul' c A := by ext u x; rfl

theorem norm_applyFieldLinear_le (A : C(K,E →L[ℝ] F)) :
    ‖applyFieldLinear A‖ ≤ 1*‖A‖ := by
  change ‖applyField A‖ ≤ 1*‖A‖
  simpa only [one_mul] using norm_applyField_le A

/-- Pointwise application also depends continuously and linearly on the operator field. -/
def applyFieldCLM : C(K,E →L[ℝ] F) →L[ℝ] (C(K,E) →L[ℝ] C(K,F)) :=
  { applyFieldLinear (K:=K) (E:=E) (F:=F) with
    cont := by
      have hb : LipschitzWith 1 (applyFieldLinear (K:=K) (E:=E) (F:=F)) := by
        apply LipschitzWith.of_dist_le_mul
        intro A B
        rw [dist_eq_norm, ← map_sub]
        have hab : dist A B = ‖A-B‖ := dist_eq_norm A B
        rw [hab]
        simpa only [NNReal.coe_one] using norm_applyFieldLinear_le (A-B)
      exact hb.continuous }

@[simp] theorem applyFieldCLM_apply (A : C(K,E →L[ℝ] F)) :
    applyFieldCLM A = applyField A := rfl

variable [FiniteDimensional ℝ E]

/-- Uniform Taylor remainder on the compact range of a path. -/
theorem superpose_quadratic_remainder (f : E → F) (hf : ContDiff ℝ ∞ f)
    (u : C(K,E)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : C(K,E), ‖h‖ < 1 →
      ‖superpose f hf.continuous (u+h) - superpose f hf.continuous u -
        applyField (superpose (fderiv ℝ f) (hf.continuous_fderiv (by simp)) u) h‖
        ≤ C * ‖h‖ ^ 2 := by
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  obtain ⟨L,hL⟩ := hdf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0:E) (‖u‖+2)) (isCompact_closedBall (0:E) (‖u‖+2))
  refine ⟨L, L.2, fun h hh => ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg L.2 (sq_nonneg _))).2
  intro x
  change ‖f (u x+h x)-f (u x)-fderiv ℝ f (u x) (h x)‖ ≤ _
  have hu : u x ∈ closedBall (0:E) (‖u‖+2) := by
    rw [mem_closedBall, dist_zero_right]
    linarith [u.norm_coe_le_norm x]
  have hsub : closedBall (u x) ‖h‖ ⊆ closedBall (0:E) (‖u‖+2) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have hb : ‖y‖ ≤ ‖y-u x‖ + ‖u x‖ := by
      simpa only [sub_add_cancel] using norm_add_le (y-u x) (u x)
    have hy' : ‖y-u x‖ ≤ ‖h‖ := by simpa only [mem_closedBall, dist_eq_norm] using hy
    linarith [u.norm_coe_le_norm x]
  have hb : ∀ y ∈ closedBall (u x) ‖h‖,
      ‖fderiv ℝ f y - fderiv ℝ f (u x)‖ ≤ (L:ℝ)*‖h‖ := by
    intro y hy
    exact (hL.norm_sub_le (hsub hy) hu).trans
      (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hy) L.2)
  have hm := (convex_closedBall (u x) ‖h‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y _ => hf.differentiable (by simp) y) hb
    (mem_closedBall_self (norm_nonneg h))
    (show u x+h x ∈ closedBall (u x) ‖h‖ by
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left] using h.norm_coe_le_norm x)
  simp only [add_sub_cancel_left] at hm
  exact hm.trans (by
    calc
      (L:ℝ)*‖h‖*‖h x‖ ≤ (L:ℝ)*‖h‖*‖h‖ :=
        mul_le_mul_of_nonneg_left (h.norm_coe_le_norm x) (mul_nonneg L.2 (norm_nonneg h))
      _ = (L:ℝ)*‖h‖^2 := by ring)

/-- The derivative of smooth pointwise composition is the pointwise derivative. -/
theorem hasFDerivAt_superpose (f : E → F) (hf : ContDiff ℝ ∞ f) (u : C(K,E)) :
    HasFDerivAt (superpose f hf.continuous)
      (applyField (superpose (fderiv ℝ f) (hf.continuous_fderiv (by simp)) u)) u := by
  obtain ⟨C,hC,hrem⟩ := superpose_quadratic_remainder f hf u
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hd : 0 < min 1 (ε/(C+1)) := lt_min zero_lt_one (div_pos hε (by positivity))
  filter_upwards [Metric.ball_mem_nhds (0:C(K,E)) hd] with h hh
  have hh' : ‖h‖ < min 1 (ε/(C+1)) := by simpa only [mem_ball, dist_zero_right] using hh
  have hsmall : C*‖h‖ ≤ ε := by
    have hmul := (lt_div_iff₀ (show 0<C+1 by positivity)).mp (lt_min_iff.mp hh').2
    nlinarith [norm_nonneg h]
  exact (hrem h (lt_min_iff.mp hh').1).trans (by nlinarith [norm_nonneg h])

theorem contDiff_superpose (f : E → F) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (superpose (K:=K) f hf.continuous) := by
  have hall : ∀ n : ℕ, ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (hf : ContDiff ℝ ∞ f),
      ContDiff ℝ n (superpose (K:=K) f hf.continuous) := by
    intro n
    induction n with
    | zero =>
      intro F _ _ f hf
      exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
        (fun u => (hasFDerivAt_superpose f hf u).continuousAt))
    | succ n ih =>
      intro F _ _ f hf
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
      refine ⟨fun u => (hasFDerivAt_superpose f hf u).differentiableAt, by simp, ?_⟩
      have hdf := (contDiff_infty_iff_fderiv.mp hf).2
      have heq : fderiv ℝ (superpose (K:=K) f hf.continuous) =
          fun u => applyFieldCLM (superpose (fderiv ℝ f) hdf.continuous u) := by
        funext u
        exact (hasFDerivAt_superpose f hf u).fderiv
      rw [heq]
      exact applyFieldCLM.contDiff.comp (ih _ _ hdf)
  exact contDiff_infty.mpr (fun n => hall n F f hf)

end OAI.Analysis.ODE.SmoothFlow
