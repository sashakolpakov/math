import OAI.Geometry.Nikodym.ManifoldMaximalBound
import OAI.Geometry.Nikodym.Riemannian.EndpointMaximal
import OAI.Geometry.Nikodym.EndpointLengthContinuity
import OAI.Geometry.Nikodym.Abstract.FiniteVolume

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
  [IsManifold 𝓘(ℝ,Space n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
    (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Space n) M]
variable {p : M} {κ : ℝ}
variable {C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
  (extChartAt 𝓘(ℝ,Space n) p p)}
variable (P : LocalBeltramiChart.ManifoldTubePatch C)

omit [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem finite_patch_volume : IsFiniteMeasure ((atlasRiemannianVolume (n:=n) p).restrict
    (C.manifoldPatch (ball 0 (2*P.radius)))) := by
  exact C.isFiniteMeasure_atlasRiemannianVolume_patch isOpen_ball.measurableSet
    (ball_subset_closedBall.trans P.target) (fun y hy => P.small y (ball_subset_closedBall hy))
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall _ _).measure_lt_top)

/-- Measurability of the actual supremum follows from compact endpoints,
closed prescribed length, null distance levels and positive tube volume;
none of these is a hypothesis on the maximal function. -/
theorem measurable_endpointNikodymMaximal (ell : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (f : M → ℂ) (hf : Integrable f ((atlasRiemannianVolume (n:=n) p).restrict
      (C.manifoldPatch (ball 0 (2*P.radius))))) :
    Measurable (P.endpointNikodymMaximal ell δ f) := by
  let := P.finite_patch_volume
  have ht : closedBall (0 : Space n) P.radius ⊆ C.manifoldChart.target := by
    rw [C.manifoldChart_target]
    exact P.core_target
  have hsmall : ∀ y ∈ closedBall (0 : Space n) P.radius, |κ| * ‖y‖^2 ≤ 1/2 :=
    fun y hy => P.small y (closedBall_subset_closedBall (by linarith [P.radius_pos]) hy)
  apply measurable_atlas_endpoint_metric_maximal p (C.isOpen_manifoldPatch isOpen_ball)
    (fun x hx => C.manifoldChart_source_subset_ext hx.1) C.manifoldChart ht
    _ hδ (isClosed_fixed_beltramiSegmentLength hsmall ell) f hf
  intro ab
  let t : Icc (0 : ℝ) 1 := ⟨0,by norm_num⟩
  refine ⟨endpointCurve C.manifoldChart ab t,mem_range_self t,?_⟩
  exact C.manifoldPatch_mono (closedBall_subset_ball (by linarith [P.radius_pos]))
    (P.endpoint_range_core ab (mem_range_self t))

/-- The local fixed-length Nikodym estimate with the actual ambient
Riemannian distance and volume, for every Lⁿ input. All geometric and
measurability prerequisites have been proved. -/
theorem endpointNikodymMaximal_bound (hn : 2 ≤ n)
    {ε ell : ℝ} (hε : 0 < ε) (hell : 0 < ell) (hell1 : ell ≤ 1/4) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ P.width → ∀ f : M → ℂ,
      MemLp f n ((atlasRiemannianVolume (n:=n) p).restrict
        (C.manifoldPatch (ball 0 (2*P.radius)))) →
      MemLp (P.endpointNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
      eLpNorm (P.endpointNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ≤
      ENNReal.ofReal (B*δ^(-ε))*eLpNorm f n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) := by
  let := P.finite_patch_volume
  obtain ⟨B,hB,hbound⟩ := P.endpointNikodymMaximal_bound_of_measurable hn hε hell hell1
  refine ⟨B,hB,?_⟩
  intro δ hδ hδP f hf
  have hnf : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  exact hbound δ hδ hδP f hf
    (P.measurable_endpointNikodymMaximal ell hδ f (hf.integrable hnf)).aestronglyMeasurable

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
