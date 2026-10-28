import OAI.Geometry.Nikodym.ManifoldEndpoints
import OAI.Geometry.Nikodym.Abstract.ChartVolume
import OAI.Geometry.Nikodym.MetricEstimate
import OAI.Analysis.Fourier.LocalSmoothing.FurtherResults

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

/-- The local maximal operator over actual inverse-chart segments of a
fixed Riemannian length. The compact endpoint range is the fixed core. -/
def endpointNikodymMaximal (ell δ : ℝ) (f : M → ℂ) : M → ℝ≥0∞ :=
  metricTubeMaximal (atlasRiemannianVolume (n:=n) p)
    (C.manifoldPatch (ball 0 (2*P.radius)))
    (fun (_ : M) (ab : EndpointParameters (Space n) P.radius) => range (endpointCurve C.manifoldChart ab))
    (fun x ab => beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell ∧
      x ∈ range (endpointCurve C.manifoldChart ab)) δ f

omit [BorelSpace M] [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
theorem endpointNikodymMaximal_eq_full (ell : ℝ) {δ : ℝ} (hδ : δ ≤ P.width)
    (f : M → ℂ) (x : M) :
    P.endpointNikodymMaximal ell δ f x =
      ⨆ ab : EndpointParameters (Space n) P.radius,
        ⨆ (_ : beltramiSegmentLength κ (ab.1 : Space n) (ab.2 : Space n) = ell ∧
          x ∈ range (endpointCurve C.manifoldChart ab)),
          (∫⁻ y in metricTube δ (range (endpointCurve C.manifoldChart ab)),
            ‖f y‖ₑ ∂atlasRiemannianVolume (n:=n) p) /
            atlasRiemannianVolume (n:=n) p (metricTube δ (range (endpointCurve C.manifoldChart ab))) := by
  apply metricTubeMaximal_eq_untruncated_of_margin _ P.ambient_margin
  · intro x ab _
    exact P.endpoint_range_core ab
  · exact hδ

omit [IsContinuousRiemannianBundle (Space n) fun x : M ↦ TangentSpace 𝓘(ℝ, Space n) x] [IsRiemannianManifold 𝓘(ℝ, Space n) M] in
/-- The analytic estimate with every metric, volume, segment-length and
tube-margin input discharged. Measurability is supplied separately by the
compact endpoint-family theorem. -/
theorem endpointNikodymMaximal_bound_of_measurable (hn : 2 ≤ n)
    {ε ell : ℝ} (hε : 0 < ε) (hell : 0 < ell) (hell1 : ell ≤ 1/4) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ P.width → ∀ f : M → ℂ,
      MemLp f n ((atlasRiemannianVolume (n:=n) p).restrict
        (C.manifoldPatch (ball 0 (2*P.radius)))) →
      AEStronglyMeasurable (P.endpointNikodymMaximal ell δ f)
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) →
      MemLp (P.endpointNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
      eLpNorm (P.endpointNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) ≤
      ENNReal.ofReal (B*δ^(-ε))*eLpNorm f n
        ((atlasRiemannianVolume (n:=n) p).restrict (C.manifoldPatch (ball 0 (2*P.radius)))) := by
  have ht : ball (0 : Space n) (2*P.radius) ⊆ C.chart.target :=
    ball_subset_closedBall.trans P.target
  obtain ⟨a,b,ha,hb,hup,hdown⟩ := C.exists_atlasRiemannianVolume_patch_constants
    isOpen_ball.measurableSet ht (fun y hy => P.small y (ball_subset_closedBall hy))
  have hback : MapsTo C.manifoldInverse (ball (0 : Space n) (2*P.radius))
      (C.manifoldPatch (ball 0 (2*P.radius))) := by
    intro y hy
    exact ⟨C.manifoldInverse_mem (ht hy),by
      simpa only [mem_preimage,C.manifoldForward_inverse (ht hy)] using hy⟩
  obtain ⟨B,hB,hbound⟩ := metricTubeMaximal_bound OAI.Analysis.Fourier.LocalSmoothing.nikodym_maximal hn hε
    (atlasRiemannianVolume (n:=n) p) (C.isOpen_manifoldPatch isOpen_ball).measurableSet
    isOpen_ball.measurableSet C.measurable_manifoldForward C.measurable_manifoldInverse
    P.one_le_K P.one_le_L P.forward_lipschitz (P.inverse_lipschitz.mono ball_subset_closedBall)
    (fun y hy => hy.2) hback (fun y hy => C.manifoldInverse_forward hy.1)
    (fun y hy => C.manifoldForward_inverse (ht hy)) ha hb hup hdown
    (show 0 < ell/3 by positivity)
  refine ⟨B,hB,?_⟩
  intro δ hδ hδP f hf hm
  exact hbound δ hδ (P.scaled_width_le hδP) _ _ _
    (fun x hx ab hadm => P.endpoint_admissible_geometry hell hell1 hδP x ab hadm) f hf hm

end OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch
