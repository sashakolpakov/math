import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Poisson
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.CutoffEstimate

/-! Unconditional localized flat-boundary Schauder estimates for small
Hölder perturbations of the Laplacian. -/

noncomputable section
open Set Metric Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem halfspace_cutoff_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ P > 0, ∀ (χ : EuclideanSpace ℝ (Fin m) → ℝ)
      (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2 →
      ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u →
      (∀ x, x k = 0 → u x = 0) →
      ∀ (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
        (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      (∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) →
      (∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) →
      (∀ x, 0 ≤ x k → χ x ≠ 0 →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B
      let G := cutoffJetForcing hα.le hα1.le A χ hχ hχc F U V
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤ 2 * P * ‖G‖ * ‖x - y‖ ^ α := by
  obtain ⟨P, hP, hPoisson⟩ := halfspace_poisson_schauder hm k hα hα1 hR
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR B hsmall u hu hz F U V hU hV heq
  exact halfspace_cutoff_estimate_of_poisson k hα.le hα1.le hR.le hP.le χ hχ hχc hχR
    (fun v hv hs hz => hPoisson v (hv.of_le (by norm_num)) hs hz)
    B hsmall u hu hz F U V hU hV heq

end OAI.Analysis.PDE.Schauder
