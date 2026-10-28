import OAI.Analysis.PDE.Schauder.Calculus.Interior.CutoffInterpolation
import OAI.Analysis.PDE.Schauder.Calculus.Interior.Cutoff

open Set Metric
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance interiorLocalCutoffMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance interiorLocalCutoffMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- A local interior estimate with an arbitrarily small top-order error.
No extensions of the solution jets or auxiliary forcing bounds are assumed. -/
theorem fullspace_localized_hessian_interpolation (hm : 3 ≤ m) (k : Fin m)
    {R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ P > 0, ∀ (χ : E → ℝ) (_ : ContDiff ℝ 3 χ) (_ : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ N ε : ℝ, 0 ≤ N → 0 < ε → ∃ D > 0,
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2 →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B‖ ≤ N →
      ∀ u : E → ℝ, ContDiff ℝ 3 u → HasCompactSupport u →
      ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) H M, 0 ≤ H → 0 ≤ M →
      (∀ x, |u x| ≤ M) →
      (∀ x, ∀ y,
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      (∀ x, χ x ≠ 0 →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      ∀ x, ∀ y,
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖ ^ α := by
  obtain ⟨P, hP, hlocal⟩ := fullspace_cutoff_schauder hm k hα hα1 hR.le
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR N ε hN hε
  obtain ⟨D, hD, hinterp⟩ := fullspace_cutoff_forcing_interpolation k hα hα1.le
    χ hχ hχc hN (div_pos hε (show 0 < 2 * P by positivity))
  refine ⟨2 * P * D, by positivity, ?_⟩
  intro B hsmall hBN u hu huc F H M hH hM hbound hh heq
  let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B
  obtain ⟨U, V, hU, hV, hG⟩ := hinterp u (hu.of_le (by norm_num)) huc H M
    hH hM hbound hh A hBN F
  have hloc := hlocal χ hχ hχc hχR B hsmall u hu F U V hU hV heq
  intro x y
  have hmul := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 * P by positivity)
  have hscale : 2 * P * (ε / (2 * P) * H + D * (‖F‖ + M)) =
      ε * H + (2 * P * D) * (‖F‖ + M) := by
    field_simp

  rw [hscale] at hmul
  exact (hloc x y).trans
    (mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
