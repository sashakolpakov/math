import OAI.Analysis.PDE.Elliptic.Boundary.Chart.Constants
import OAI.Analysis.PDE.Schauder.Boundary.SchauderNormalization

open Set Filter InnerProductSpace
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- A bounded normalized boundary chart with its positive side aligned
with any chosen coordinate halfspace. The orthogonal alignment preserves
the doubled chart ball, so all chart constants are fixed before the PDE
coefficients and solution are chosen. -/
theorem exists_bounded_coordinate_chart {m : ℕ} (k : Fin m)
    {r : EuclideanSpace ℝ (Fin m) → ℝ} (hr : ContDiff ℝ 3 r)
    (x : EuclideanSpace ℝ (Fin m)) (hg : fderiv ℝ r x ≠ 0)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ (c C : ℝ) (G P : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      0 < c ∧ 1 ≤ C ∧ ContDiff ℝ 3 G ∧ ContDiff ℝ 3 P ∧ G 0 = x ∧
      ∀ z ∈ Metric.closedBall 0 2,
        G z ∈ U ∧ (fun y => P (G y)) =ᶠ[𝓝 z] id ∧
        r (G z) - r x = -c * z k ∧
        ‖fderiv ℝ G z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 G z‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 G z‖ ≤ C ∧ ‖fderiv ℝ P (G z)‖ ≤ C := by
  let E := EuclideanSpace ℝ (Fin m)
  obtain ⟨v, c, C₀, G₀, P₀, hv, hc, _, hG₀, hP₀, hGzero, hchart⟩ :=
    exists_bounded_normalized_chart hr x hg hU hxU
  let e : E := EuclideanSpace.single k 1
  have he : ‖e‖ = 1 := by
    change ‖(EuclideanSpace.single k (1 : ℝ) : EuclideanSpace ℝ (Fin m))‖ = 1
    simp
  let Q := Submodule.reflection (ℝ ∙ (e - v))ᗮ
  have hQ : Q e = v := Submodule.reflection_sub (he.trans hv.symm)
  let G := fun y : E => G₀ (Q y)
  let P := fun y : E => Q.symm (P₀ y)
  have hG : ContDiff ℝ 3 G := hG₀.comp Q.contDiff
  have hP : ContDiff ℝ 3 P := Q.symm.contDiff.comp hP₀
  obtain ⟨C₁, hC₁, hB₁⟩ := compact_C3_derivative_bounds hG (isCompact_closedBall (0 : E) 2)
  obtain ⟨C₂, _, hB₂⟩ := compact_C3_derivative_bounds hP
    ((isCompact_closedBall (0 : E) 2).image hG.continuous)
  refine ⟨c, max C₁ C₂, G, P, hc, hC₁.trans (le_max_left _ _), hG, hP, ?_, ?_⟩
  · simpa only [G, map_zero] using hGzero
  intro z hz
  have hzQ : Q z ∈ Metric.closedBall 0 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, Q.norm_map] using hz
  have hch := hchart (Q z) hzQ
  have hinv : (fun y => P (G y)) =ᶠ[𝓝 z] id := by
    have hh := hch.2.1.comp_tendsto (Q.continuous.tendsto z)
    filter_upwards [hh] with y hy
    change Q.symm (P₀ (G₀ (Q y))) = y
    change P₀ (G₀ (Q y)) = Q y at hy
    rw [hy, Q.symm_apply_apply]
  have hnormal : inner ℝ v (Q z) = z k := by
    rw [← hQ, Q.inner_map_map]
    change inner ℝ (EuclideanSpace.single k (1 : ℝ)) z = z k
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul]
  have hB := hB₁ z hz
  have hBP := hB₂ (G z) ⟨z, hz, rfl⟩
  refine ⟨hch.1, hinv, ?_, hB.1.trans (le_max_left _ _),
    hB.2.1.trans (le_max_left _ _), hB.2.2.trans (le_max_left _ _),
    hBP.1.trans (le_max_right _ _)⟩
  exact hch.2.2.1.trans (congrArg (fun t : ℝ => -c * t) hnormal)

end OAI.Analysis.PDE.Elliptic
