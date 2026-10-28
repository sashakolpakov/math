import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.DiskFactorizationOn
import Mathlib.Analysis.Analytic.Polynomial

/-! # Closed Disk Factorization -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ClosedDiskFactorization.Constructions.DiskFactorization

noncomputable section

/-!
# Closed-disk factorization and actual contour root moments

If there are no boundary zeros, the analytic unit extends across the circle.
The resulting local identities justify taking logarithmic derivatives in
the contour formulas, starting from the original analytic function.
-/

open Set Filter _root_.Metric _root_.Polynomial
open scoped _root_.Topology BigOperators

theorem exists_polynomial_unit_on_closedDisk {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hn : ∃ z ∈ ball c R, f z ≠ 0)
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ P : Polynomial ℂ, P.Monic ∧ (∀ z, P.eval z = 0 → z ∈ ball c R) ∧
      ∃ u : ℂ → ℂ, AnalyticOnNhd ℂ u (closedBall c R) ∧
        (∀ z ∈ closedBall c R, u z ≠ 0) ∧
        ∀ z ∈ closedBall c R, f =ᶠ[𝓝 z] (fun w => P.eval w * u w) := by
  classical
  obtain ⟨P, hP, hPr, g, hg, hgn, hfg⟩ := DiskFactorizationOn.Constructions.DiskFactorization.exists_polynomial_unit_on_disk hf hn
  let u : ℂ → ℂ := fun z => if P.eval z = 0 then g z else f z / P.eval z
  have hu : EqOn u g (ball c R) := by
    intro z hz
    by_cases hpz : P.eval z = 0
    · simp [u, hpz]
    · simp [u, hpz, hfg z hz]
  have hu_div {z : ℂ} (hpz : P.eval z ≠ 0) :
      u =ᶠ[𝓝 z] (fun w => f w / P.eval w) := by
    filter_upwards [P.continuous.continuousAt.eventually_ne hpz] with w hw
    simp only [u, ite_eq_right hw]
  refine ⟨P, hP, hPr, u, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzi : z ∈ ball c R
    · apply (hg z hzi).congr
      filter_upwards [isOpen_ball.mem_nhds hzi] with w hw
      exact (hu hw).symm
    · have hpz : P.eval z ≠ 0 := fun h => hzi (hPr z h)
      exact ((hf z hz).div (AnalyticOnNhd.eval_polynomial P z (mem_univ z)) hpz).congr
        (hu_div hpz).symm
  · intro z hz
    by_cases hzi : z ∈ ball c R
    · rw [hu hzi]
      exact hgn z hzi
    · have hpz : P.eval z ≠ 0 := fun h => hzi (hPr z h)
      have hzs : z ∈ sphere c R := by
        apply mem_sphere.mpr
        exact le_antisymm (mem_closedBall.mp hz) (not_lt.mp hzi)
      exact (by simpa only [u, ite_eq_right hpz] using div_ne_zero (hboundary z hzs) hpz)
  · intro z hz
    by_cases hzi : z ∈ ball c R
    · filter_upwards [isOpen_ball.mem_nhds hzi] with w hw
      rw [hu hw]
      exact hfg w hw
    · have hpz : P.eval z ≠ 0 := fun h => hzi (hPr z h)
      filter_upwards [P.continuous.continuousAt.eventually_ne hpz] with w hw
      simp only [u, ite_eq_right hw]
      field_simp

theorem exists_root_tuple_unit_on_closedDisk {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hn : ∃ z ∈ ball c R, f z ≠ 0)
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ (d : ℕ) (roots : Fin d → ℂ) (u : ℂ → ℂ),
      (∀ i, roots i ∈ ball c R) ∧ AnalyticOnNhd ℂ u (closedBall c R) ∧
      (∀ z ∈ closedBall c R, u z ≠ 0) ∧
      ∀ z ∈ closedBall c R, f =ᶠ[𝓝 z] (fun w => RootMomentsNe.Constructions.RootMoments.rootProduct roots w * u w) := by
  obtain ⟨P, hP, hPr, u, hu, hun, hfu⟩ := exists_polynomial_unit_on_closedDisk hf hn hboundary
  obtain ⟨d, roots, hroots, hPeval⟩ := DiskFactorizationOn.Constructions.DiskFactorization.exists_root_tuple P hP
  refine ⟨d, roots, u, fun i => hPr _ (hroots i), hu, hun, ?_⟩
  intro z hz
  simpa only [hPeval] using hfu z hz

/-- Every analytic function with no boundary zeros supplies its actual
finite root tuple and all contour power sums. -/
theorem exists_contour_root_moments {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hn : ∃ z ∈ ball c R, f z ≠ 0) (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ (d : ℕ) (roots : Fin d → ℂ), (∀ i, roots i ∈ ball c R) ∧
      ∀ k : ℕ, (∮ z in C(c, R), z ^ k * logDeriv f z) =
        (2 * Real.pi * Complex.I) * ∑ i, (roots i) ^ k := by
  obtain ⟨d, roots, u, hroots, hu, hun, hfu⟩ :=
    exists_root_tuple_unit_on_closedDisk hf hn hboundary
  refine ⟨d, roots, hroots, fun k => ?_⟩
  calc
    _ = ∮ z in C(c, R), z ^ k *
        logDeriv (fun w => RootMomentsNe.Constructions.RootMoments.rootProduct roots w * u w) z := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      dsimp only
      congr 1
      exact (logDeriv_congr_nhds (hfu z (sphere_subset_closedBall hz))).eq_of_nhds
    _ = _ := RootMomentsNe.Constructions.RootMoments.integral_rootProduct_mul_nonvanishing roots hR hroots hu hun k

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ClosedDiskFactorization.Constructions.DiskFactorization
