import OAI.Analysis.Fourier.Estimates

open OAI.Analysis.Fourier.Wave

/-! Orthogonal invariance of the exact polar surface measure used in the
restriction statements. No replacement probability measure is introduced. -/

open _root_.MeasureTheory Set Metric
open scoped Pointwise ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem sphereMeasure_apply_cone {n : ℕ} {s : Set (Space n)} (hs : MeasurableSet s) :
    OAI.Analysis.Fourier.Restriction.sphereMeasure n s = (n : ℝ≥0∞) *
      volume (Ioo (0 : ℝ) 1 • (s ∩ sphere (0 : Space n) 1)) := by
  have he : (Subtype.val : sphere (0 : Space n) 1 → Space n) ''
      ((Subtype.val : sphere (0 : Space n) 1 → Space n) ⁻¹' s) =
      s ∩ sphere (0 : Space n) 1 := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
    · rintro ⟨hx, hxS⟩
      exact ⟨⟨x, hxS⟩, hx, rfl⟩
  rw [OAI.Analysis.Fourier.Restriction.sphereMeasure, Measure.map_apply measurable_subtype_coe hs,
    Measure.toSphere_apply' _ (hs.preimage measurable_subtype_coe), he]
  simp [Space]

theorem volume_preimage_orthogonal {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (s : Set (Space n)) : volume (e ⁻¹' s) = volume s := by
  calc
    _ = (Measure.map e volume) s := (e.toHomeomorph.measurableEmbedding.map_apply _ _).symm
    _ = _ := congrArg (fun μ : Measure (Space n) => μ s) e.measurePreserving.map_eq

theorem orthogonal_preimage_cone {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n)
    (s : Set (Space n)) :
    Ioo (0 : ℝ) 1 • ((e ⁻¹' s) ∩ sphere (0 : Space n) 1) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (s ∩ sphere (0 : Space n) 1)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, hy, rfl⟩
    refine ⟨r, hr, e y, ⟨hy.1, ?_⟩, ?_⟩
    · simpa only [mem_sphere, dist_zero_right, e.norm_map] using hy.2
    · simp only [map_smul]
  · rintro ⟨r, hr, y, hy, he⟩
    refine ⟨r, hr, e.symm y, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_preimage, e.apply_symm_apply] using hy.1
    · simpa only [mem_sphere, dist_zero_right, e.symm.norm_map] using hy.2
    · apply e.injective
      simpa only [map_smul, e.apply_symm_apply] using he

theorem measurePreserving_sphere_orthogonal {n : ℕ}
    (e : Space n ≃ₗᵢ[ℝ] Space n) :
    MeasurePreserving e (OAI.Analysis.Fourier.Restriction.sphereMeasure n) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  refine ⟨e.continuous.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.continuous.measurable hs,
    sphereMeasure_apply_cone (hs.preimage e.continuous.measurable),
    orthogonal_preimage_cone, volume_preimage_orthogonal, sphereMeasure_apply_cone hs]

end OAI.Analysis.Fourier.Radial
