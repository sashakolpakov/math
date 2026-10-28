import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
open Set _root_.MeasureTheory Manifold Filter
open scoped Topology ContDiff

namespace OAI.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) 1 M]

/-- A null set in one ordinary smooth chart is null in every overlapping chart.
No measurability of the set is required. -/
theorem chart_image_null_of_chart_image_null (μ : Measure E) [μ.IsAddHaarMeasure]
    (p q : M) {S : Set M}
    (hp : S ⊆ (extChartAt 𝓘(ℝ,E) p).source)
    (hq : S ⊆ (extChartAt 𝓘(ℝ,E) q).source)
    (hnull : μ (extChartAt 𝓘(ℝ,E) q '' S) = 0) :
    μ (extChartAt 𝓘(ℝ,E) p '' S) = 0 := by
  have hd : DifferentiableOn ℝ
      (extChartAt 𝓘(ℝ,E) p ∘ (extChartAt 𝓘(ℝ,E) q).symm)
      (extChartAt 𝓘(ℝ,E) q '' S) := by
    apply (contDiffOn_ext_coord_change (I := 𝓘(ℝ,E)) (n := 1) p q).differentiableOn
      (by norm_num) |>.mono
    rintro y ⟨x, hx, rfl⟩
    refine ⟨(extChartAt 𝓘(ℝ,E) q).map_source (hq hx), ?_⟩
    change (extChartAt 𝓘(ℝ,E) q).symm (extChartAt 𝓘(ℝ,E) q x) ∈
      (extChartAt 𝓘(ℝ,E) p).source
    simpa only [PartialEquiv.left_inv _ (hq hx)] using hp hx
  have he : (extChartAt 𝓘(ℝ,E) p ∘ (extChartAt 𝓘(ℝ,E) q).symm) ''
      (extChartAt 𝓘(ℝ,E) q '' S) = extChartAt 𝓘(ℝ,E) p '' S := by
    rw [image_image]
    apply image_congr
    intro x hx
    simp only [Function.comp_apply, PartialEquiv.left_inv _ (hq hx)]
  rw [← he]
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ hd hnull

/-- Locally null chart images give a null image in any fixed chart. Countability
is used only in the finite-dimensional coordinate space, not on the manifold. -/
theorem chart_image_null_of_locally_chart_null (μ : Measure E) [μ.IsAddHaarMeasure]
    (p : M) (S : Set M)
    (hloc : ∀ x ∈ S, ∃ q : M, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ,E) q).source ∧
      μ (extChartAt 𝓘(ℝ,E) q '' (S ∩ U)) = 0) :
    μ (extChartAt 𝓘(ℝ,E) p '' (S ∩ (extChartAt 𝓘(ℝ,E) p).source)) = 0 := by
  apply measure_null_of_locally_null
  rintro y ⟨x, ⟨hxS, hxp⟩, rfl⟩
  obtain ⟨q, U, hU, hxU, hUq, hnull⟩ := hloc x hxS
  let T := (S ∩ U) ∩ (extChartAt 𝓘(ℝ,E) p).source
  have hT : μ (extChartAt 𝓘(ℝ,E) p '' T) = 0 := by
    apply chart_image_null_of_chart_image_null μ p q
      (fun _ hx => hx.2) (fun _ hx => hUq hx.1.2)
    exact measure_mono_null (image_mono inter_subset_left) hnull
  refine ⟨extChartAt 𝓘(ℝ,E) p '' T, ?_, hT⟩
  have hpre : (extChartAt 𝓘(ℝ,E) p).symm ⁻¹' U ∈
      𝓝 (extChartAt 𝓘(ℝ,E) p x) :=
    extChartAt_preimage_mem_nhds' hxp (hU.mem_nhds hxU)
  apply Filter.mem_of_superset
    (inter_mem (mem_nhdsWithin_of_mem_nhds hpre) self_mem_nhdsWithin)
  rintro z ⟨hzU, w, ⟨hwS, hwp⟩, rfl⟩
  refine ⟨w, ⟨⟨hwS, ?_⟩, hwp⟩, rfl⟩
  simpa only [mem_preimage, PartialEquiv.left_inv _ hwp] using hzU

/-- Convenient form when the local chart is centered at the point itself. -/
theorem chart_image_null_of_locally_centered_chart_null
    (μ : Measure E) [μ.IsAddHaarMeasure] (p : M) (S : Set M)
    (hloc : ∀ x ∈ S, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ,E) x).source ∧
      μ (extChartAt 𝓘(ℝ,E) x '' (S ∩ U)) = 0) :
    μ (extChartAt 𝓘(ℝ,E) p '' (S ∩ (extChartAt 𝓘(ℝ,E) p).source)) = 0 := by
  apply chart_image_null_of_locally_chart_null μ p S
  intro x hx
  obtain ⟨U, hU⟩ := hloc x hx
  exact ⟨x, U, hU⟩

end OAI.Geometry.Riemannian
