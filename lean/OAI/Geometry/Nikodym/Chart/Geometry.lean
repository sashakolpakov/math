import Mathlib

noncomputable section
namespace OAI.Geometry.Nikodym

open Set _root_.MeasureTheory
open scoped ENNReal

variable {M N : Type*} [MetricSpace M] [MetricSpace N]

/-- Metric tube, written with its distance witness so it applies in both
Riemannian and Euclidean charts without a compactness assumption. -/
def metricTube (r : ℝ) (I : Set M) : Set M :=
  {x | ∃ y ∈ I, dist x y < r}

theorem metricTube_eq_thickening (r : ℝ) (I : Set M) :
    metricTube r I = Metric.thickening r I := by
  ext x
  simp only [metricTube,Set.mem_ofPred_eq,Metric.mem_thickening_iff]

/-- A Lipschitz chart maps a metric tube into the corresponding enlarged
Euclidean tube. Only points in the chart are used. -/
theorem image_metricTube_subset {K : NNReal} {f : M → N} {S I : Set M}
    (hf : LipschitzOnWith K f S) (hI : I ⊆ S) {r : ℝ} (hK : 0 < K) :
    f '' (metricTube r I ∩ S) ⊆ metricTube ((K : ℝ)*r) (f '' I) := by
  rintro _ ⟨x,⟨⟨y,hy,hd⟩,hx⟩,rfl⟩
  refine ⟨f y,⟨y,hy,rfl⟩,?_⟩
  exact (hf.dist_le_mul x hx y (hI hy)).trans_lt
    (mul_lt_mul_of_pos_left hd (show (0 : ℝ) < K from hK))

/-- The inverse chart gives the reverse tube inclusion. The surrounding
region is explicit, so no tube escaping a coordinate patch is ignored. -/
theorem metricTube_inter_subset_image {L : NNReal} {f : M → N} {g : N → M}
    {S I : Set M} {T : Set N} (hg : LipschitzOnWith L g T)
    (hI : I ⊆ S) (hmap : MapsTo f S T)
    (hgf : ∀ x ∈ S, g (f x) = x) (hfg : ∀ y ∈ T, f (g y) = y)
    (hback : MapsTo g T S) {r : ℝ} (hL : 0 < L) :
    metricTube r (f '' I) ∩ T ⊆ f '' (metricTube ((L : ℝ)*r) I ∩ S) := by
  rintro y ⟨⟨_,⟨x,hx,rfl⟩,hd⟩,hy⟩
  refine ⟨g y,⟨⟨x,hx,?_⟩,hback hy⟩,hfg y hy⟩
  rw [← hgf x (hI hx)]
  exact (hg.dist_le_mul y hy (f x) (hmap (hI hx))).trans_lt
    (mul_lt_mul_of_pos_left hd (show (0 : ℝ) < L from hL))

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

/-- Exact quantitative comparison of one-dimensional intersection measures
under a chart with Lipschitz inverse. This supplies the positive-length
intersection input needed for Nikodym dimension transfer. -/
theorem hausdorff_one_intersection_chart_bounds
    {K L : NNReal} {f : M → N} {g : N → M} {S I E : Set M} {T : Set N}
    (hf : LipschitzOnWith K f S) (hg : LipschitzOnWith L g T)
    (hI : I ⊆ S) (hmap : MapsTo f S T) (hinv : ∀ x ∈ S, g (f x) = x) :
    Measure.hausdorffMeasure 1 (f '' (E ∩ I)) ≤
      (K : ℝ≥0∞) * Measure.hausdorffMeasure 1 (E ∩ I) ∧
    Measure.hausdorffMeasure 1 (E ∩ I) ≤
      (L : ℝ≥0∞) * Measure.hausdorffMeasure 1 (f '' (E ∩ I)) := by
  have hEI : E ∩ I ⊆ S := inter_subset_right.trans hI
  constructor
  · simpa using (hf.mono hEI).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1)
  · have himage : f '' (E ∩ I) ⊆ T := by
      rintro _ ⟨x,hx,rfl⟩
      exact hmap (hEI hx)
    have hsub : E ∩ I ⊆ g '' (f '' (E ∩ I)) := by
      intro x hx
      exact ⟨f x,⟨x,hx,rfl⟩,hinv x (hEI hx)⟩
    exact (measure_mono hsub).trans (by
      simpa using (hg.mono himage).hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1))

end OAI.Geometry.Nikodym
