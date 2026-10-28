import OAI.Geometry.Nikodym.IntrinsicChartMaps
import OAI.Geometry.Nikodym.Riemannian.VolumeChart

noncomputable section
open Set _root_.MeasureTheory
open scoped ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart

variable {n : ℕ}
variable {g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))} {κ : ℝ}
  {x₀ : EuclideanSpace ℝ (Fin n)}
variable (C : LocalBeltramiChart g κ x₀)

/-- The genuine intrinsic Riemannian volume, pushed through the constructed
Beltrami chart, is exactly the volume of the Beltrami metric. -/
theorem map_intrinsicVolume_source :
    Measure.map C.intrinsicForward
      ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict C.intrinsicSource) =
      (beltramiVolume κ).restrict C.chart.target := by
  classical
  let F := C.chart.source.piecewise C.chart (fun _ => 0)
  have hF : Measurable F := C.chart.continuousOn.measurable_piecewise
    continuousOn_const C.chart.open_source.measurableSet
  have hc := (OAI.Geometry.Nikodym.IntrinsicDomain.measurableEmbedding_coordinate g).measurable
  have hm : Measure.map (OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g)
      ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict C.intrinsicSource) =
      g.coordinateVolume.restrict C.chart.source := by
    rw [← OAI.Geometry.Nikodym.IntrinsicDomain.map_intrinsicVolume g,Measure.restrict_map hc
      C.chart.open_source.measurableSet]
    rfl
  change Measure.map (F ∘ OAI.Geometry.Nikodym.IntrinsicDomain.coordinate g)
    ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict C.intrinsicSource) = _
  rw [← Measure.map_map hF hc,hm]
  calc
    Measure.map F (g.coordinateVolume.restrict C.chart.source) =
        Measure.map C.chart (g.coordinateVolume.restrict C.chart.source) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem C.chart.open_source.measurableSet] with x hx
      exact piecewise_eq_of_mem _ _ _ hx
    _ = _ := C.map_volume_source

theorem intrinsicForward_image_eq {A : Set (IntrinsicDomain g)}
    (hA : A ⊆ C.intrinsicSource) :
    C.intrinsicForward '' A = C.chart.target ∩ C.intrinsicInverse ⁻¹' A := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨C.intrinsicForward_mem (hA hx),by
      simpa only [mem_preimage,C.intrinsicInverse_forward (hA hx)] using hx⟩
  · rintro ⟨hy,hx⟩
    exact ⟨C.intrinsicInverse y,hx,C.intrinsicForward_inverse hy⟩

theorem measurableSet_intrinsicForward_image {A : Set (IntrinsicDomain g)}
    (hAm : MeasurableSet A) (hA : A ⊆ C.intrinsicSource) :
    MeasurableSet (C.intrinsicForward '' A) := by
  rw [C.intrinsicForward_image_eq hA]
  exact C.chart.open_target.measurableSet.inter
    (C.measurable_intrinsicInverse hAm)

theorem map_intrinsicVolume_restrict {A : Set (IntrinsicDomain g)}
    (hAm : MeasurableSet A) (hA : A ⊆ C.intrinsicSource) :
    Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict A) =
      (beltramiVolume κ).restrict (C.intrinsicForward '' A) := by
  have him := C.measurableSet_intrinsicForward_image hAm hA
  have hsub : C.intrinsicForward '' A ⊆ C.chart.target := by
    rintro _ ⟨x,hx,rfl⟩
    exact C.intrinsicForward_mem (hA hx)
  have hpre : C.intrinsicForward ⁻¹' (C.intrinsicForward '' A) ∩
      C.intrinsicSource = A := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,hxy⟩,hx⟩
      have he : y = x := by
        have := congrArg C.intrinsicInverse hxy
        simpa only [C.intrinsicInverse_forward (hA hy),
          C.intrinsicInverse_forward hx] using this
      exact he ▸ hy
    · intro hx
      exact ⟨⟨x,hx,rfl⟩,hA hx⟩
  have h := congrArg (fun μ => μ.restrict (C.intrinsicForward '' A))
    C.map_intrinsicVolume_source
  rw [Measure.restrict_map C.measurable_intrinsicForward him,
    Measure.restrict_restrict (C.measurable_intrinsicForward him),hpre,
    Measure.restrict_restrict him,inter_eq_left.mpr hsub] at h
  exact h

theorem intrinsicVolume_eq_beltramiVolume_image {A : Set (IntrinsicDomain g)}
    (hAm : MeasurableSet A) (hA : A ⊆ C.intrinsicSource) :
    OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g A = beltramiVolume κ (C.intrinsicForward '' A) := by
  have h := congrArg (fun μ => μ Set.univ) (C.map_intrinsicVolume_restrict hAm hA)
  simpa only [Measure.map_apply C.measurable_intrinsicForward MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] using h

theorem intrinsicForward_image_patch {V : Set (EuclideanSpace ℝ (Fin n))}
    (hV : V ⊆ C.chart.target) :
    C.intrinsicForward '' (C.intrinsicSource ∩ C.intrinsicForward ⁻¹' V) = V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx.2
  · intro hy
    exact ⟨C.intrinsicInverse y,⟨C.intrinsicInverse_mem (hV hy),by
      simpa only [mem_preimage,C.intrinsicForward_inverse (hV hy)] using hy⟩,
      C.intrinsicForward_inverse (hV hy)⟩

theorem map_intrinsicVolume_patch {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target) :
    Measure.map C.intrinsicForward ((OAI.Geometry.Nikodym.IntrinsicDomain.intrinsicVolume g).restrict
      (C.intrinsicSource ∩ C.intrinsicForward ⁻¹' V)) =
      (beltramiVolume κ).restrict V := by
  rw [C.map_intrinsicVolume_restrict
    (C.isOpen_intrinsicSource.measurableSet.inter (C.measurable_intrinsicForward hVm))
    inter_subset_left,C.intrinsicForward_image_patch hV]

end OAI.Geometry.Nikodym.LocalBeltramiChart
