import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SchauderLift
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.EvenHolder
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SupportBounds
import OAI.Analysis.PDE.Schauder.Boundary.Jet.Lift

/-! The sharp, unconditional flat-boundary Poisson estimate. The forcing need
not vanish on the boundary: its actual Hölder trace is lifted first. -/

noncomputable section
open Set Metric InnerProductSpace Laplacian
namespace OAI.Analysis.PDE.Schauder

theorem laplacian_zero_outside_support {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (x) (hx : x ∉ tsupport u) :
    laplacian u x = 0 := by
  simp only [laplacian_coordinate, hessian_zero_outside_support u x hx,
    zero_apply, Finset.sum_const_zero]

theorem halfspace_poisson_schauder {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α R : ℝ} (hα : 0 < α) (hα1 : α < 1) (hR : 0 < R) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 u → tsupport u ⊆ closedBall 0 R →
      (∀ x, x k = 0 → u x = 0) →
      ∀ H, 0 ≤ H →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        |laplacian u x - laplacian u y| ≤ H * ‖x - y‖ ^ α) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          C * H * ‖x - y‖ ^ α := by
  obtain ⟨C₀, hC₀, hbase⟩ := halfspace_schauder_from_lift hm k hα hα1
  obtain ⟨C₁, hC₁, hlift⟩ := exists_boundary_jet_lift_function k hα hα1 hR
  let B := C₁ * (1 + (2 * R + 1) ^ α)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C₀ * (1 + m * B) + B, by positivity, ?_⟩
  intro u hu hs hz H hH hh
  have huc : HasCompactSupport u :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).of_isClosed_subset (isClosed_tsupport u) hs
  have hsLap (x) (hx : R < ‖x‖) : laplacian u x = 0 := by
    apply laplacian_zero_outside_support u x
    intro hxs
    have : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hs hxs
    linarith
  obtain ⟨F, hF, hFs, hFn⟩ := exists_halfspace_holder_extension
    (EuclideanSpace.single k 1) (by simp) (laplacian u)
    (continuous_laplacian_of_two u hu) hR.le hα.le hH hsLap (by
      intro x hx y hy
      exact hh x (by simpa [EuclideanSpace.inner_single_left] using hx)
        y (by simpa [EuclideanSpace.inner_single_left] using hy))
  obtain ⟨W, hW, hWc, hWz, _, hWlap, hWh⟩ := hlift F hFs
  have hbound : C₁ * ‖F‖ ≤ B * H := by
    exact (mul_le_mul_of_nonneg_left hFn hC₁.le).trans_eq (by dsimp [B]; ring)
  have hWmatch (x) (hx : x k = 0) : laplacian W x = laplacian u x := by
    rw [hWlap x hx]
    exact hF x (by simp [EuclideanSpace.inner_single_left, hx])
  have hWH (x) (_hx : 0 ≤ x k) (y) (_hy : 0 ≤ y k) :
      ‖fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y‖ ≤ (B * H) * ‖x-y‖ ^ α :=
    (hWh x y).trans (mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg (norm_nonneg _) _))
  intro x hx y hy
  have hb := hbase u W hu hW huc hWc hz hWz hWmatch H (B * H) hH (by positivity)
    hh hWH x hx y hy
  exact hb.trans_eq (by ring)

end OAI.Analysis.PDE.Schauder
