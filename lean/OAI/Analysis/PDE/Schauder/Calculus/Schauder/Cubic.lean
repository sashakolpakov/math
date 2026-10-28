import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceEstimate
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.DifferenceLimit
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! A genuine C²,α-to-C³ upgrade for C¹,α elliptic data. -/

noncomputable section
open Set Metric
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Weak

local instance cubicMatrixNG (m : ℕ) : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance cubicMatrixNS (m : ℕ) : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))
local instance cubicMatrixDerivativeNG (m : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))
local instance cubicMatrixDerivativeNS (m : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → Fin m → ℝ)))

theorem small_coefficient_C3 {m : ℕ} (hm : 3 ≤ m) {α R : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hB : ∀ x, x ∉ closedBall 0 R → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = 0)
    (hhalf : 2 * ((m : ℝ) * m * ‖B‖) * ‖poissonHolderOperator hm hα hα1 R‖ ≤ 1 / 2)
    (hPD : ∀ x, (1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef)
    (hBc : ContDiff ℝ 1 (OAI.Analysis.Normed.Function.Holder.HolderMap.value B))
    (DB : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m))
      (EuclideanSpace ℝ (Fin m) →L[ℝ] Matrix (Fin m) (Fin m) ℝ) α)
    (hDB : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DB x = fderiv ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap.value B) x)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    (Df V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hDf : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Df x = fderiv ℝ f x)
    (hV : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanHessian m) α)
    (hH : ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) x)
    (heq : ∀ x, nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = f x)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R)
    {Ω : Set (EuclideanSpace ℝ (Fin m))} (hΩ : IsOpen Ω) (hχone : ∀ x ∈ Ω, χ x = 1) :
    ContDiffOn ℝ 3 u Ω := by
  obtain ⟨C, _, hC⟩ := difference_solution_schauder_bound hm hα hα1 B hB hhalf hPD
    hBc DB hDB u f hu hf Df V hDf hV H hH heq χ hχ hχc hχR
  have hdir (v : EuclideanSpace ℝ (Fin m)) : ContDiffOn ℝ 2 (fun x => fderiv ℝ u x v) Ω := by
    have hc := contDiff_directional_derivative_of_schauder_bound hα u χ
      (hu.differentiable (by norm_num)) v (hC v)
    exact hc.contDiffOn.congr (fun x hx => by rw [hχone x hx, one_mul])
  change ContDiffOn ℝ (2 + 1) u Ω
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  refine ⟨fun x _ => (hu.differentiable (by norm_num) x).differentiableWithinAt, by simp, ?_⟩
  exact contDiffOn_clm_apply.mpr hdir

end OAI.Analysis.PDE.Schauder
