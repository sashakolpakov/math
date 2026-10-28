import OAI.Geometry.Kakeya.Quadratic.CompressionDimension

open Set Module
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compact curved Kakeya sets with the specified direction set,
translation set, and complete parameter interval. -/
def HasQuadraticCurves (B : E →ₗ[ℝ] E) (τ : ℝ) (Y W : Set E) (K : Set (E × ℝ)) : Prop :=
  IsCompact K ∧ ∀ y ∈ Y, ∃ w ∈ W, ∀ t ∈ Icc (-τ) τ, curve B y w t ∈ K

/-- Every compact direction set admits the sharp-dimensional compact
compression example, in a sufficiently large fixed translation ball.
The lower dimension bound is proved separately using the actual lift. -/
theorem exists_compact_compression (B : E →ₗ[ℝ] E) {Y : Set E} (hY : IsCompact Y)
    (τ : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ R' : ℝ, R ≤ R' → ∃ K : Set (E × ℝ),
      HasQuadraticCurves B τ Y (Metric.closedBall 0 R') K ∧
      dimH K ≤ (finrank ℝ E -
        (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) := by
  let : IsClosed (compressionSubspace B : Set E) := (compressionSubspace B).closed_of_finiteDimensional
  obtain ⟨P, C, hPB, hPC, hQC, hsur⟩ := exists_compression_maps B
  have hCc : Continuous C := C.continuous_of_finiteDimensional
  obtain ⟨R, hR⟩ := (hY.image hCc).isBounded.subset_closedBall (0 : E)
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro R' hR'
  let K : Set (E × ℝ) := (fun p : E × ℝ => curve B p.1 (C p.1) p.2) ''
    (Y ×ˢ Icc (-τ) τ)
  have hcont : Continuous (fun p : E × ℝ => curve B p.1 (C p.1) p.2) := by
    have hBc : Continuous B := B.continuous_of_finiteDimensional
    unfold curve
    fun_prop
  refine ⟨K, ⟨(hY.prod isCompact_Icc).image hcont, ?_⟩, ?_⟩
  · intro y hy
    refine ⟨C y, ?_, ?_⟩
    · exact (Metric.closedBall_subset_closedBall ((le_max_left R 1).trans hR'))
        (hR (mem_image_of_mem C hy))
    · intro t ht
      exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩
  · have hsub : K ⊆ ruledConstraint (D := CompressionSpace B) P (compressionSubspace B).mkQ := by
      rintro z ⟨⟨y, t⟩, hp, rfl⟩
      exact compressed_curve_equation B P C hPB hPC hQC y t
    exact (dimH_mono hsub).trans (by
      simpa only [finrank_compressionSpace] using
        dimH_ruledConstraint (D := CompressionSpace B) P _ hsur)

end OAI.Geometry.Kakeya.Quadratic
