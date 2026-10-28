import OAI.Analysis.PDE.Schauder.Dirichlet.CutoffInterpolation
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.CutoffSchauder

open Set Metric
open scoped Topology Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {m : ℕ} {α : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance localCutoffMatrixGroup : NormedAddCommGroup (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (Fin m → Fin m → ℝ))
local instance localCutoffMatrixSpace : NormedSpace ℝ (Matrix (Fin m) (Fin m) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (Fin m → Fin m → ℝ))

/-- A local boundary estimate with an arbitrarily small top-order error.
No extensions of the solution jets or auxiliary forcing bounds are assumed. -/
theorem halfspace_localized_hessian_interpolation (hm : 3 ≤ m) (k : Fin m)
    {R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ P > 0, ∀ (χ : E → ℝ) (_ : ContDiff ℝ 3 χ) (_ : HasCompactSupport χ),
      tsupport χ ⊆ closedBall 0 R →
      ∀ N ε : ℝ, 0 ≤ N → 0 < ε → ∃ D > 0,
      ∀ B : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α,
      P * (m : ℝ) * m * ‖B‖ * (1 + (2 * R + 1) ^ α) ≤ 1 / 2 →
      ‖OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B‖ ≤ N →
      ∀ u : E → ℝ, ContDiff ℝ 3 u → HasCompactSupport u →
      (∀ x, x k = 0 → u x = 0) →
      ∀ (F : OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α) H M, 0 ≤ H → 0 ≤ M →
      (∀ x, 0 ≤ x k → |u x| ≤ M) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x-y‖ ^ α) →
      (∀ x, 0 ≤ x k → χ x ≠ 0 →
        nondivergenceOperator (fun y => 1 - OAI.Analysis.Normed.Function.Holder.HolderMap.value B y) u x = OAI.Analysis.Normed.Function.Holder.HolderMap.value F x) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) x -
          fderiv ℝ (fderiv ℝ (fun z => χ z * u z)) y‖ ≤
            (ε * H + D * (‖F‖ + M)) * ‖x-y‖ ^ α := by
  obtain ⟨P, hP, hlocal⟩ := halfspace_cutoff_schauder hm k hα hα1 hR
  refine ⟨P, hP, ?_⟩
  intro χ hχ hχc hχR N ε hN hε
  obtain ⟨D, hD, hinterp⟩ := halfspace_cutoff_forcing_interpolation k hα hα1.le
    χ hχ hχc hN (div_pos hε (show 0 < 2 * P by positivity))
  refine ⟨2 * P * D, by positivity, ?_⟩
  intro B hsmall hBN u hu huc hz F H M hH hM hbound hh heq
  let A := OAI.Analysis.Normed.Function.Holder.HolderMap.constant (1 : Matrix (Fin m) (Fin m) ℝ) - B
  obtain ⟨U, V, hU, hV, hG⟩ := hinterp u (hu.of_le (by norm_num)) huc H M
    hH hM hbound hh A hBN F
  have hloc := hlocal χ hχ hχc hχR B hsmall u hu hz F U V hU hV heq
  intro x hx y hy
  have hmul := mul_le_mul_of_nonneg_left hG (show 0 ≤ 2 * P by positivity)
  have hscale : 2 * P * (ε / (2 * P) * H + D * (‖F‖ + M)) =
      ε * H + (2 * P * D) * (‖F‖ + M) := by
    field_simp

  rw [hscale] at hmul
  exact (hloc x hx y hy).trans
    (mul_le_mul_of_nonneg_right hmul (Real.rpow_nonneg (norm_nonneg _) _))

/-- A larger cutoff leaves all derivatives unchanged where the smaller
cutoff is supported. This is the germ needed for nested localization. -/
theorem nested_cutoff_germ {χ η u : E → ℝ}
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    {x : E} (hx : χ x ≠ 0) : (fun y => η y * u y) =ᶠ[𝓝 x] u := by
  have hx' : x ∈ tsupport χ := subset_closure hx
  filter_upwards [hη x hx'] with y hy
  simp only [hy, one_mul]

theorem nested_cutoff_product {χ η u : E → ℝ}
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) :
    (fun x => χ x * (η x * u x)) = (fun x => χ x * u x) := by
  funext x
  by_cases hx : χ x = 0
  · simp only [hx, zero_mul]
  · rw [(nested_cutoff_germ hη hx).eq_of_nhds]

theorem nested_cutoff_operator {χ η u : E → ℝ}
    (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1)
    (A : E → Matrix (Fin m) (Fin m) ℝ) {x : E} (hx : χ x ≠ 0) :
    nondivergenceOperator A (fun y => η y * u y) x = nondivergenceOperator A u x := by
  have h := ((nested_cutoff_germ (u := u) hη hx).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  simp only [nondivergenceOperator, h]

end OAI.Analysis.PDE.Schauder
