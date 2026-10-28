import OAI.Geometry.Nikodym.AtlasMaps
import OAI.Geometry.Nikodym.IntrinsicVolume

noncomputable section
open Set _root_.MeasureTheory Manifold Bundle
open scoped ContDiff

namespace OAI.Geometry.Nikodym

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin n))
    (fun x : M => TangentSpace 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) x)]

/-- Riemannian volume restricted to the chosen ordinary atlas chart.
It is defined by the determinant of the actual pulled-back metric and is
extended by zero outside the chart, not by an independently chosen measure. -/
def atlasRiemannianVolume (p : M) : Measure M :=
  Measure.map (atlasInverse (E:=EuclideanSpace ℝ (Fin n)) p)
    (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume

omit [MeasurableSpace M] [BorelSpace M] in
theorem ae_mem_abstractChartMetric (p : M) :
    ∀ᵐ y ∂(abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume,
      y ∈ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).target := by
  rw [← OAI.Geometry.Nikodym.IntrinsicDomain.coordinateVolume_restrict_domain
    (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p)]
  exact ae_restrict_mem (isOpen_extChartAt_target p).measurableSet

theorem ae_mem_atlasRiemannianVolume (p : M) :
    ∀ᵐ x ∂atlasRiemannianVolume (n:=n) p,
      x ∈ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source := by
  apply (ae_map_iff (measurable_atlasInverse p).aemeasurable
    (isOpen_extChartAt_source p).measurableSet).mpr
  exact Filter.Eventually.of_forall (atlasInverse_mem p)

theorem atlasRiemannianVolume_restrict_source (p : M) :
    (atlasRiemannianVolume (n:=n) p).restrict
      (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source =
      atlasRiemannianVolume (n:=n) p :=
  Measure.restrict_eq_self_of_ae_mem (ae_mem_atlasRiemannianVolume p)

/-- Ordinary atlas coordinates recover precisely the determinant density. -/
theorem map_atlasRiemannianVolume (p : M) :
    Measure.map (atlasForward (E:=EuclideanSpace ℝ (Fin n)) p)
      (atlasRiemannianVolume (n:=n) p) =
      (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume := by
  rw [atlasRiemannianVolume,Measure.map_map (measurable_atlasForward p)
    (measurable_atlasInverse p)]
  calc
    Measure.map (atlasForward p ∘ atlasInverse p)
        (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume =
      Measure.map id (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume := by
      apply Measure.map_congr
      filter_upwards [ae_mem_abstractChartMetric p] with y hy
      exact atlasForward_inverse p hy
    _ = _ := Measure.map_id

theorem map_atlasRiemannianVolume_restrict (p : M) {A : Set M}
    (hAm : MeasurableSet A)
    (hA : A ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source) :
    Measure.map (atlasForward (E:=EuclideanSpace ℝ (Fin n)) p)
      ((atlasRiemannianVolume (n:=n) p).restrict A) =
      (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume.restrict
        (atlasForward (E:=EuclideanSpace ℝ (Fin n)) p '' A) := by
  let F := atlasForward (E:=EuclideanSpace ℝ (Fin n)) p
  let S := (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source
  have him := measurableSet_atlasForward_image p hAm hA
  have hpre : F ⁻¹' (F '' A) ∩ S = A := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,hxy⟩,hx⟩
      have he : y = x := by
        have := congrArg (atlasInverse p) hxy
        simpa only [F,atlasInverse_forward p (hA hy),atlasInverse_forward p hx] using this
      exact he ▸ hy
    · intro hx
      exact ⟨⟨x,hx,rfl⟩,hA hx⟩
  have h := congrArg (fun μ => μ.restrict (F '' A)) (map_atlasRiemannianVolume p)
  rw [Measure.restrict_map (measurable_atlasForward p) him] at h
  rw [← atlasRiemannianVolume_restrict_source p,
    Measure.restrict_restrict ((measurable_atlasForward p) him),hpre] at h
  exact h

theorem atlasRiemannianVolume_eq_coordinateVolume_image (p : M) {A : Set M}
    (hAm : MeasurableSet A)
    (hA : A ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source) :
    atlasRiemannianVolume (n:=n) p A =
      (abstractChartMetric (E:=EuclideanSpace ℝ (Fin n)) p).coordinateVolume
        (atlasForward (E:=EuclideanSpace ℝ (Fin n)) p '' A) := by
  have h := congrArg (fun μ => μ Set.univ) (map_atlasRiemannianVolume_restrict p hAm hA)
  simpa only [Measure.map_apply (measurable_atlasForward p) MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] using h

end OAI.Geometry.Nikodym
