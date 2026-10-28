import OAI.MeasureTheory.Kakeya.Geometry
import OAI.Analysis.Fourier.Restriction.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace OAI.MeasureTheory.Kakeya

def openNeighborhood {n : ℕ} (δ : ℝ) (F : Set (Space n)) : Set (Space n) :=
  ⋃ x ∈ F, Metric.ball x δ

theorem isOpen_openNeighborhood {n : ℕ} (δ : ℝ) (F : Set (Space n)) :
    IsOpen (openNeighborhood δ F) :=
  isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball

theorem tube_subset_openNeighborhood {n : ℕ} {δ : ℝ} {F : Set (Space n)}
    {ω x : Space n} (hF : OAI.MeasureTheory.Kakeya.unitSegment ω x ⊆ F) :
    OAI.MeasureTheory.Kakeya.tube δ ω x ⊆ openNeighborhood δ F := by
  intro y hy
  rcases mem_tube_iff.mp hy with ⟨t, ht, hyt⟩
  exact Set.mem_iUnion.mpr ⟨x + t • ω,
    Set.mem_iUnion.mpr ⟨hF ⟨t, ht, rfl⟩, hyt⟩⟩

theorem ae_sphereMeasure_norm (n : ℕ) :
    ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n, ‖ω‖ = 1 := by
  unfold OAI.Analysis.Fourier.Restriction.sphereMeasure
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet).mpr
  exact Eventually.of_forall fun ω ↦ by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.property

theorem kakeya_neighborhood_maximal_lower {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {F : Set (Space n)} (hF : OAI.MeasureTheory.Kakeya.IsKakeyaSet F) :
    ∀ᵐ ω ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n,
      1 ≤ OAI.MeasureTheory.Kakeya.kakeyaMaximal δ ((openNeighborhood δ F).indicator (fun _ ↦ (1 : ℂ))) ω := by
  filter_upwards [ae_sphereMeasure_norm n] with ω hω
  obtain ⟨x, hx⟩ := hF ω hω
  exact one_le_kakeyaMaximal_indicator hδ (tube_subset_openNeighborhood hx)

/-- The maximal conjecture forces the expected lower-volume inequality for
every finite-volume neighbourhood of a Kakeya set. This is the uniform-scale
part of the dimension argument; variable-scale Hausdorff covers need a further
dyadic decomposition. -/
theorem kakeyaMaximal_implies_neighborhood_bound (hK : OAI.MeasureTheory.Kakeya.KakeyaMaximalConjecture)
    (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ F : Set (Space n),
      OAI.MeasureTheory.Kakeya.IsKakeyaSet F → volume (openNeighborhood δ F) ≠ ∞ →
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ) ^ (1 / (n : ℝ)) ≤
        ENNReal.ofReal (C * δ ^ (-ε)) *
          volume (openNeighborhood δ F) ^ (1 / (n : ℝ)) := by
  obtain ⟨C, hC, hCf⟩ := hK n hn ε hε
  refine ⟨C, hC, fun δ hδ hδ1 F hF hfinite ↦ ?_⟩
  have hmeas := (isOpen_openNeighborhood δ F).measurableSet
  let f : Space n → ℂ := (openNeighborhood δ F).indicator (fun _ ↦ 1)
  have hf : MemLp f n := memLp_indicator_const n hmeas 1 (.inr hfinite)
  obtain ⟨_, hbound⟩ := hCf δ hδ hδ1 f hf
  have hlo : eLpNorm (fun _ : Space n ↦ (1 : ℝ≥0∞)) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
      eLpNorm (OAI.MeasureTheory.Kakeya.kakeyaMaximal δ f) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    apply eLpNorm_mono_enorm_ae aestronglyMeasurable_const
    exact kakeya_neighborhood_maximal_lower hδ hF
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hninf : (n : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top n
  have hnorm : eLpNorm f n volume = volume (openNeighborhood δ F) ^ (1 / (n : ℝ)) := by
    simpa only [f, enorm_one, one_mul, ENNReal.toReal_natCast] using
      (eLpNorm_indicator_const (c := (1 : ℂ)) hmeas.nullMeasurableSet hn0 hninf)
  have hone : eLpNorm (fun _ : Space n ↦ (1 : ℝ≥0∞)) n (OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      OAI.Analysis.Fourier.Restriction.sphereMeasure n Set.univ ^ (1 / (n : ℝ)) := by
    simpa only [enorm_eq_self, one_mul, ENNReal.toReal_natCast] using
      (eLpNorm_const' (μ := OAI.Analysis.Fourier.Restriction.sphereMeasure n) (1 : ℝ≥0∞) hn0 hninf)
  rw [← hone, ← hnorm]
  exact hlo.trans hbound

end OAI.MeasureTheory.Kakeya
