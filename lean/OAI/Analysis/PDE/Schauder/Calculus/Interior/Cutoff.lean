import OAI.Analysis.PDE.Schauder.Calculus.Interior.Perturbation
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.CutoffEquation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Compact

/-! A full-space localized estimate matching the boundary perturbation API. -/

noncomputable section
open Set Metric Laplacian
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

theorem fullspace_cutoff_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) :
    ∃ P > 0, ∀ (χ : EuclideanSpace ℝ (Fin m) → ℝ)
      (hχ : ContDiff ℝ 3 χ) (hχc : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (Matrix (Fin m) (Fin m) ℝ) α,
      P*(m:ℝ)*m*‖B‖*(1+(2*R+1)^α) ≤ 1/2 →
      ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ 3 u →
      ∀ (F U : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
        (V : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) α),
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value U x = u x) →
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ u x) →
      (∀ x, χ x ≠ 0 → nondivergenceOperator (fun y => 1-OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ)-B
      let G := cutoffJetForcing hα.le hα1.le A χ hχ hχc F U V
      ∀ x y,
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) x - fderiv ℝ (fderiv ℝ (fun z => χ z*u z)) y‖ ≤
          2*P*‖G‖*‖x-y‖^α := by
  obtain ⟨P, hP, hPoisson⟩ := compact_schauder_estimate_C2 hm hα hα1
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR B hsmall u hu F U V hU hV heq
  let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ)-B
  let G := cutoffJetForcing hα.le hα1.le A χ hχ hχc F U V
  have hAval : (OAI.Analysis.Normed.Function.Holder.HolderMap.value A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ) =
      (fun y => 1-OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) := by funext y; rfl
  have hactual (x) : nondivergenceOperator (fun y => 1-OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) (fun z => χ z*u z) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value G x := by
    rw [← hAval]
    exact cutoffJetForcing_equation_at hα.le hα1.le A χ u hχ hχc (hu.of_le (by norm_num)) F U V x
      (hU x) (hV x) (fun hn => by rw [hAval]; exact heq x hn)
  have hs : tsupport (fun z => χ z*u z) ⊆ closedBall 0 R := tsupport_mul_subset_left.trans hχR
  apply fullspace_small_coefficients k (fun z => χ z*u z) (hχ.mul hu) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B)
    hR hα.le hα1.le hP.le (norm_nonneg B) (norm_nonneg B) (norm_nonneg G) hs
  · exact OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le B
  · intro x y
    simpa only [dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le B x y
  · intro x y
    rw [hactual, hactual]
    simpa only [Real.norm_eq_abs, dist_eq_norm] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le G x y
  · intro K hK hLap x y
    exact hPoisson _ ((hχ.mul hu).of_le (by norm_num)) hχc.mul_right K hK hLap y x
  · nlinarith only [hsmall]

end OAI.Analysis.PDE.Schauder
