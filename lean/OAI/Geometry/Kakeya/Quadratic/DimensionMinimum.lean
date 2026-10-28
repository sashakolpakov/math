import OAI.Geometry.Kakeya.Quadratic.DimensionLower

open Set _root_.MeasureTheory Metric Module
open scoped Topology ENNReal

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The exact minimum, including attainment by a compact set.  Every
sufficiently large fixed translation ball works. -/
theorem quadratic_dimension_minimum (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    (hn : 1 ≤ finrank ℝ E) (B : E →ₗ[ℝ] E) {τ : ℝ} (hτ : 0 < τ)
    {Y : Set E} (hYc : IsCompact Y) (hY : (0 : E) ∈ interior Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' →
      IsLeast (dimH '' {K : Set (E × ℝ) | HasQuadraticCurves B τ Y (closedBall 0 R') K})
        (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) := by
  obtain ⟨R, hR, hupper⟩ := exists_compact_compression B hYc τ
  refine ⟨R, hR, ?_⟩
  intro R' hR'
  have hlower (K : Set (E × ℝ)) (h : HasQuadraticCurves B τ Y (closedBall 0 R') K) :
      (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) ≤ dimH K := by
    apply dimH_quadratic_curves_lower hK hn B hτ hY
    intro y hy
    obtain ⟨w, hw, hcurve⟩ := h.2 y hy
    exact ⟨w, hcurve⟩
  obtain ⟨K, hKcurves, hKdim⟩ := hupper R' hR'
  refine ⟨⟨K, hKcurves, le_antisymm hKdim (hlower K hKcurves)⟩, ?_⟩
  rintro d ⟨K', hK', rfl⟩
  exact hlower K' hK'

/-- The infimum formula and a compact attaining set, stated together. -/
theorem quadratic_dimension_infimum_attained (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    (hn : 1 ≤ finrank ℝ E) (B : E →ₗ[ℝ] E) {τ : ℝ} (hτ : 0 < τ)
    {Y : Set E} (hYc : IsCompact Y) (hY : (0 : E) ∈ interior Y) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' →
      sInf (dimH '' {K : Set (E × ℝ) | HasQuadraticCurves B τ Y (closedBall 0 R') K}) =
        (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) ∧
      ∃ K : Set (E × ℝ), HasQuadraticCurves B τ Y (closedBall 0 R') K ∧
        dimH K = (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) := by
  obtain ⟨R, hR, hmin⟩ := quadratic_dimension_minimum hK hn B hτ hYc hY
  refine ⟨R, hR, ?_⟩
  intro R' hR'
  exact ⟨(hmin R' hR').csInf_eq, (hmin R' hR').1⟩

end OAI.Geometry.Kakeya.Quadratic
