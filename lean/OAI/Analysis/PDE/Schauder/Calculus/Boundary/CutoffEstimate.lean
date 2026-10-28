import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SmallCoefficients
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.CutoffEquation

/-! Localizing the halfspace Poisson estimate before coefficient freezing.
The Poisson premise is an explicit intermediate input, separated from the
algebraic cutoff and perturbation steps. -/

noncomputable section
open Set Metric Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem halfspace_cutoff_estimate_of_poisson {m : ℕ} (k : Fin m) {α R P : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R) (hP : 0 ≤ P)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ)
    (hχR : tsupport χ ⊆ closedBall 0 R)
    (hPoisson : ∀ v : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ 3 v →
      tsupport v ⊆ closedBall 0 R → (∀ x, x k = 0 → v x = 0) →
      ∀ H, 0 ≤ H →
        (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k → |laplacian v x - laplacian v y| ≤ H * ‖x - y‖ ^ α) →
        ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
          ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ ≤ P * H * ‖x - y‖ ^ α)
    (B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α)
    (hsmall : P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x, x k = 0 → u x = 0)
    (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α)
    (hU : ∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x)
    (hV : ∀ x, 0 ≤ x k → OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x)
    (heq : ∀ x, 0 ≤ x k → χ x ≠ 0 →
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) :
    let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B
    let G := cutoffJetForcing hα hα1 A χ hχ hχc F U V
    ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
        fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤ 2 * P * ‖G‖ * ‖x - y‖ ^ α := by
  let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B
  let G := cutoffJetForcing hα hα1 A χ hχ hχc F U V
  have hAval : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) =
      (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) := by
    funext y
    rfl
  have hactual (x) (hx : 0 ≤ x k) :
      nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) (fun z => χ z * u z) x =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value G x := by
    rw [← hAval]
    exact cutoffJetForcing_equation_at hα hα1 A χ u hχ hχc (hu.of_le (by norm_num)) F U V x
      (hU x hx) (hV x hx) (fun hne => by rw [hAval]; exact heq x hx hne)
  have hs : tsupport (fun z => χ z * u z) ⊆ closedBall 0 R :=
    tsupport_mul_subset_left.trans hχR
  apply halfspace_small_coefficients k (fun z => χ z * u z) (hχ.mul hu) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B)
    hR hα hα1 hP (norm_nonneg B) (norm_nonneg B) (norm_nonneg G) hs
  · intro x _
    exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le B x
  · intro x _ y _
    simpa only [dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le B x y
  · intro x hx y hy
    rw [hactual x hx, hactual y hy]
    simpa only [Real.norm_eq_abs, dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le G x y
  · exact hPoisson _ (hχ.mul hu) hs (fun x hx => by simp only [hz x hx, mul_zero])
  · nlinarith only [hsmall]

end OAI.Analysis.PDE.Schauder
