import OAI.Geometry.Nikodym.Abstract.ChartVolume

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
variable {p : M} {κ : ℝ}
variable (C : LocalBeltramiChart (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p) κ
  (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p p))

theorem atlasRiemannianVolume_patch_lt_top {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target)
    (hsmall : ∀ y ∈ V, |κ| * ‖y‖^2 ≤ 1/2) (hfin : volume V < ⊤) :
    atlasRiemannianVolume (n:=n) p
      (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V) < ⊤ := by
  rw [C.atlasRiemannianVolume_eq_beltramiVolume_image
    (C.manifoldChart.open_source.measurableSet.inter (C.measurable_manifoldForward hVm))
    inter_subset_left,C.manifoldForward_image_patch hV]
  have hup := (beltramiVolume_restrict_bounds hVm hsmall).2 Set.univ
  simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,
    Measure.smul_apply,smul_eq_mul] at hup
  exact lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

/-- The finite-measure premise needed for continuity of tube averages follows
from boundedness of the actual chart, with the genuine Riemannian measure. -/
theorem isFiniteMeasure_atlasRiemannianVolume_patch
    {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target)
    (hsmall : ∀ y ∈ V, |κ| * ‖y‖^2 ≤ 1/2) (hfin : volume V < ⊤) :
    IsFiniteMeasure ((atlasRiemannianVolume (n:=n) p).restrict
      (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V)) := by
  rw [isFiniteMeasure_restrict]
  exact (C.atlasRiemannianVolume_patch_lt_top hVm hV hsmall hfin).ne

end OAI.Geometry.Nikodym.LocalBeltramiChart
