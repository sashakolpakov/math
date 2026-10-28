import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Laplacian
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Compact

/-! The sharp flat-boundary Schauder estimate when the forcing has zero trace. -/

noncomputable section
open Set Metric InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem halfspace_schauder_zero_trace_forcing {m : ℕ} (hm : 3 ≤ m)
    (k : Fin m) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (u : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, x k = 0 → u x = 0) →
      (∀ x, x k = 0 → laplacian u x = 0) →
      ∀ H, 0 ≤ H →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        |laplacian u x - laplacian u y| ≤ H * ‖x - y‖ ^ α) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * H * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := compact_schauder_estimate_C2 hm hα hα1
  refine ⟨2 * C, by positivity, ?_⟩
  intro u hu huc hz hl H hH hh x hx y hy
  let e := EuclideanSpace.single k (1 : ℝ)
  let U := oddNormalExtension e u
  have hU : ContDiff ℝ 2 U := contDiff_odd_of_boundary_laplacian_zero k u hu hz hl
  have hUc : HasCompactSupport U := hasCompactSupport_oddNormalExtension e u huc
  have hLap (a b : EuclideanSpace ℝ (Fin m)) :
      |laplacian U a - laplacian U b| ≤ (2 * H) * ‖a - b‖ ^ α := by
    change |laplacian (oddNormalExtension (EuclideanSpace.single k 1) u) a -
      laplacian (oddNormalExtension (EuclideanSpace.single k 1) u) b| ≤ _
    rw [laplacian_oddNormalExtension k u hu hz hl, laplacian_oddNormalExtension k u hu hz hl]
    apply oddNormalExtension_holder _ (by simp) _ hα.le hH
    · intro z hz'
      exact hl z (by simpa [EuclideanSpace.inner_single_left] using hz')
    · intro a ha b hb
      exact hh a (by simpa [EuclideanSpace.inner_single_left] using ha)
        b (by simpa [EuclideanSpace.inner_single_left] using hb)
  have hnormal (z) (hz' : inner ℝ e z = 0) : fderiv ℝ (fderiv ℝ u) z e e = 0 := by
    have heq : z k = 0 := by simpa [e, EuclideanSpace.inner_single_left] using hz'
    rw [← laplacian_eq_normal_boundary k u hu hz z heq]
    exact hl z heq
  have hzero (z) (hz' : inner ℝ e z = 0) : u z = 0 :=
    hz z (by simpa [e, EuclideanSpace.inner_single_left] using hz')
  have hsame (z) (hz' : 0 ≤ z k) : fderiv ℝ (fderiv ℝ U) z = fderiv ℝ (fderiv ℝ u) z := by
    ext v w
    change fderiv ℝ (fderiv ℝ (oddNormalExtension e u)) z v w = _
    rw [second_fderiv_oddNormalExtension e (by simp [e]) u hu hzero hnormal]
    simp [e, EuclideanSpace.inner_single_left, hz']
  have h := hb U hU hUc (2 * H) (by positivity) hLap y x
  rw [hsame x hx, hsame y hy] at h
  calc
    _ ≤ C * (2 * H) * ‖x - y‖ ^ α := h
    _ = (2 * C) * H * ‖x - y‖ ^ α := by ring

end OAI.Analysis.PDE.Schauder
