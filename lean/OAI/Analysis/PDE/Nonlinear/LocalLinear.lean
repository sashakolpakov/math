import OAI.Analysis.PDE.Nonlinear.LinearBootstrap
import OAI.Analysis.PDE.Nonlinear.FirstJetExtension
import OAI.Analysis.PDE.Nonlinear.SmoothHolder

/-! The local linear bootstrap, stated only in terms of actual functions and derivatives. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

def HasLocalHolderBound {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F]
    (α : ℝ) (f : X → F) (x₀ : X) : Prop :=
  ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
    ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α

theorem localHolderBound_of_C1At
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x₀ : E} (hf : ContDiffAt ℝ 1 f x₀) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) : HasLocalHolderBound α f x₀ := by
  obtain ⟨H, heq⟩ := exists_C1_holder_germ f x₀ hf hα hα1
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨r, hr, ‖H‖ + 1, by positivity, ?_⟩
  intro x hx y hy
  rw [← hh hx, ← hh hy]
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le H x y).trans
  rw [dist_eq_norm]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

local instance localLinearFirstGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance localLinearFirstSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
local instance localLinearHessianGroup (m : ℕ) : NormedAddCommGroup (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance localLinearHessianSpace (m : ℕ) : NormedSpace ℝ (OAI.Analysis.PDE.Schauder.EuclideanHessian m) := inferInstance
local instance localLinearMatrixDGroup (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))
local instance localLinearMatrixDSpace (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem linear_C3At_of_local_holder {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (x₀ : EuclideanSpace ℝ (Fin m))
    (hA : ContDiffAt ℝ 1 A x₀) (hu : ContDiffAt ℝ 2 u x₀) (hf : ContDiffAt ℝ 1 f x₀)
    (hDA : HasLocalHolderBound α (fderiv ℝ A) x₀)
    (hHu : HasLocalHolderBound α (fderiv ℝ (fderiv ℝ u)) x₀)
    (hDf : HasLocalHolderBound α (fderiv ℝ f) x₀)
    (hPD : ∀ᶠ x in 𝓝 x₀, (A x).PosDef)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Schauder.nondivergenceOperator A u x = f x) :
    ContDiffAt ℝ 3 u x₀ := by
  obtain ⟨rA, hrA, CA, hCA, hhA⟩ := hDA
  obtain ⟨ru, hru, Cu, hCu, hhu⟩ := hHu
  obtain ⟨rf, hrf, Cf, hCf, hhf⟩ := hDf
  obtain ⟨gA, hgA, _, heA, VA, DA, hVA, hDVA⟩ :=
    exists_C1_holder_extension A x₀ hA hrA hα.le hα1.le hCA.le hhA
  obtain ⟨gu, hgu, _, heu, Vu, Hu, hVu, hHu⟩ :=
    exists_C2_holder_extension u x₀ hu hru hα.le hα1.le hCu.le hhu
  obtain ⟨gf, hgf, _, hef, Vf, Df, hVf, hDf⟩ :=
    exists_C1_holder_extension f x₀ hf hrf hα.le hα1.le hCf.le hhf
  have hVAfun : (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.value VA x) = gA := funext hVA
  have hVAc : ContDiff ℝ 1 (OAI.Analysis.Normed.Function.Holder.HolderMap.value VA) := by
    change ContDiff ℝ 1 (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.value VA x)
    rw [hVAfun]
    exact hgA
  have hDAc (x) : OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap.value VA) x := by
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ (fun y => OAI.Analysis.Normed.Function.Holder.HolderMap.value VA y) x
    rw [hVAfun]
    exact hDVA x
  have hevent : ∀ᶠ x in 𝓝 x₀, gA x = A x ∧ gf x = f x ∧
      fderiv ℝ (fderiv ℝ gu) x = fderiv ℝ (fderiv ℝ u) x ∧
      (A x).PosDef ∧ OAI.Analysis.PDE.Schauder.nondivergenceOperator A u x = f x := by
    filter_upwards [heA, hef, (heu.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ), hPD, hPDE]
      with x ha hf hu hp hq
    exact ⟨ha, hf, hu, hp, hq⟩
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp hevent
  have hp (x) (hx : x ∈ ball x₀ r) : (OAI.Analysis.Normed.Function.Holder.HolderMap.value VA x).PosDef := by
    rw [hVA x, (hh hx).1]
    exact (hh hx).2.2.2.1
  have hq (x) (hx : x ∈ ball x₀ r) : OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value VA) gu x = gf x := by
    unfold OAI.Analysis.PDE.Schauder.nondivergenceOperator
    rw [hVA x, (hh hx).1, (hh hx).2.2.1, (hh hx).2.1]
    exact (hh hx).2.2.2.2
  have hc := linear_C3On hm hα hα1 VA hVAc DA hDAc gu gf hgu hgf
    Vu Df Hu hVu hDf hHu isOpen_ball hq hp
  exact ((hc x₀ (mem_ball_self hr)).contDiffAt (ball_mem_nhds x₀ hr)).congr_of_eventuallyEq heu.symm

end OAI.Analysis.PDE.Nonlinear
