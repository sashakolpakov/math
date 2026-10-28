import OAI.Geometry.Nikodym.Abstract.ChartMaps
import OAI.Geometry.Nikodym.Abstract.Volume
import OAI.Geometry.Nikodym.Riemannian.VolumeChart

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

/-- The constructed manifold chart transports the actual Riemannian
volume into Beltrami volume, on every measurable part of its source. -/
theorem map_atlasRiemannianVolume_restrict {A : Set M}
    (hAm : MeasurableSet A) (hA : A ⊆ C.manifoldChart.source) :
    Measure.map C.manifoldForward ((atlasRiemannianVolume (n:=n) p).restrict A) =
      (beltramiVolume κ).restrict (C.manifoldForward '' A) := by
  classical
  let F := C.chart.source.piecewise C.chart (fun _ => 0)
  have hFm : Measurable F := C.chart.continuousOn.measurable_piecewise
    continuousOn_const C.chart.open_source.measurableSet
  have hAA : A ⊆ (extChartAt 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) p).source :=
    hA.trans C.manifoldChart_source_subset_ext
  have hImage := measurableSet_atlasForward_image p hAm hAA
  have hIS : atlasForward (E:=EuclideanSpace ℝ (Fin n)) p '' A ⊆ C.chart.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact C.atlasForward_mem_chart_source (hA hx)
  have hcomp : C.manifoldForward =ᵐ[(atlasRiemannianVolume (n:=n) p).restrict A]
      F ∘ atlasForward (E:=EuclideanSpace ℝ (Fin n)) p := by
    filter_upwards [ae_restrict_mem hAm] with x hx
    rw [C.manifoldForward_eq_chart_atlasForward (hA hx)]
    change C.chart (atlasForward p x) =
      C.chart.source.piecewise C.chart (fun _ => 0) (atlasForward p x)
    exact (piecewise_eq_of_mem _ _ _ (C.atlasForward_mem_chart_source (hA hx))).symm
  rw [Measure.map_congr hcomp,←Measure.map_map hFm (measurable_atlasForward p),
    OAI.Geometry.Nikodym.map_atlasRiemannianVolume_restrict p hAm hAA]
  calc
    Measure.map F ((abstractChartMetric p).coordinateVolume.restrict
        (atlasForward p '' A)) =
      Measure.map C.chart ((abstractChartMetric p).coordinateVolume.restrict
        (atlasForward p '' A)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hImage] with y hy
      exact piecewise_eq_of_mem _ _ _ (hIS hy)
    _ = _ := by rw [C.map_volume_restrict hImage hIS,←C.manifoldForward_image_eq hA]

theorem atlasRiemannianVolume_eq_beltramiVolume_image {A : Set M}
    (hAm : MeasurableSet A) (hA : A ⊆ C.manifoldChart.source) :
    atlasRiemannianVolume (n:=n) p A = beltramiVolume κ (C.manifoldForward '' A) := by
  have h := congrArg (fun μ => μ Set.univ) (C.map_atlasRiemannianVolume_restrict hAm hA)
  simpa only [Measure.map_apply C.measurable_manifoldForward MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter] using h

theorem map_atlasRiemannianVolume_patch {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target) :
    Measure.map C.manifoldForward ((atlasRiemannianVolume (n:=n) p).restrict
      (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V)) =
      (beltramiVolume κ).restrict V := by
  rw [C.map_atlasRiemannianVolume_restrict
    (C.manifoldChart.open_source.measurableSet.inter (C.measurable_manifoldForward hVm))
    inter_subset_left,C.manifoldForward_image_patch hV]

theorem exists_atlasRiemannianVolume_patch_constants
    {V : Set (EuclideanSpace ℝ (Fin n))}
    (hVm : MeasurableSet V) (hV : V ⊆ C.chart.target)
    (hsmall : ∀ y ∈ V, |κ| * ‖y‖^2 ≤ 1/2) :
    ∃ a b : ℝ≥0∞, a ≠ ⊤ ∧ b ≠ ⊤ ∧
      Measure.map C.manifoldForward ((atlasRiemannianVolume (n:=n) p).restrict
        (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V)) ≤ b • volume ∧
      volume.restrict V ≤ a •
        Measure.map C.manifoldForward ((atlasRiemannianVolume (n:=n) p).restrict
          (C.manifoldChart.source ∩ C.manifoldForward ⁻¹' V)) := by
  rw [C.map_atlasRiemannianVolume_patch hVm hV]
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((2/3 : ℝ)^(n+1)))
  let b : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt ((2 : ℝ)^(n+1)))
  have ha : 0 < a := ENNReal.ofReal_pos.mpr
    (Real.sqrt_pos.mpr (pow_pos (by norm_num) _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨hlo,hup⟩ := beltramiVolume_restrict_bounds hVm hsmall
  refine ⟨a⁻¹,b,ENNReal.inv_ne_top.mpr ha.ne',ENNReal.ofReal_ne_top,?_,?_⟩
  · exact hup.trans (smul_le_smul_left b Measure.restrict_le_self)
  · have h : a⁻¹ • (a • volume.restrict V) ≤
        a⁻¹ • (beltramiVolume κ).restrict V := smul_le_smul_left a⁻¹ hlo
    simpa only [smul_smul,ENNReal.inv_mul_cancel ha.ne' hat,one_smul] using h

theorem volume_manifoldForward_image_pos {A : Set M}
    (hAm : MeasurableSet A) (hA : A ⊆ C.manifoldChart.source)
    (hsmall : ∀ y ∈ C.manifoldForward '' A, |κ| * ‖y‖^2 ≤ 1/2)
    (hpos : 0 < atlasRiemannianVolume (n:=n) p A) :
    0 < volume (C.manifoldForward '' A) := by
  rw [C.atlasRiemannianVolume_eq_beltramiVolume_image hAm hA] at hpos
  have hup := (beltramiVolume_restrict_bounds
    (C.measurableSet_manifoldForward_image hAm hA) hsmall).2 Set.univ
  simp only [Measure.restrict_apply MeasurableSet.univ,univ_inter,
    Measure.smul_apply,smul_eq_mul] at hup
  by_contra h
  have hz : volume (C.manifoldForward '' A) = 0 := le_antisymm (le_of_not_gt h) bot_le
  rw [hz,mul_zero] at hup
  exact (not_lt_of_ge hup) hpos

end OAI.Geometry.Nikodym.LocalBeltramiChart
