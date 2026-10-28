import OAI.Geometry.Nikodym.ManifoldMaximal
import OAI.Geometry.Nikodym.Abstract.Sectional

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym

open OAI.Geometry.Nikodym

/-- The local fixed-length maximal estimate in the compact endpoint
parametrization. The chart and quantitative patch are constructed from
scalar sectional curvature. The operator uses genuine ambient Riemannian
tubes, metric arclength, and determinant volume. -/
theorem local_endpoint_nikodym_maximal
    {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (Space n) M] [MeasurableSpace M] [BorelSpace M]
    [IsManifold 𝓘(ℝ,Space n) ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ,Space n) ∞ (Space n)
      (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsContinuousRiemannianBundle (Space n) (fun x : M => TangentSpace 𝓘(ℝ,Space n) x)]
    [IsRiemannianManifold 𝓘(ℝ,Space n) M]
    (hn : 2 ≤ n) (p : M) {κ : ℝ}
    (hκ : (abstractChartMetric (E:=Space n) p).HasConstantSectionalCurvature κ) :
    ∃ (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
        (extChartAt 𝓘(ℝ,Space n) p p)) (P : OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch C),
      ∀ ε ell : ℝ, 0 < ε → 0 < ell → ell ≤ 1/4 →
        ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ P.width → ∀ f : M → ℂ,
          MemLp f n ((atlasRiemannianVolume (n:=n) p).restrict
            (C.manifoldPatch (ball 0 (2*P.radius)))) →
          MemLp (P.endpointNikodymMaximal ell δ f) n
            ((atlasRiemannianVolume (n:=n) p).restrict
              (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
          eLpNorm (P.endpointNikodymMaximal ell δ f) n
            ((atlasRiemannianVolume (n:=n) p).restrict
              (C.manifoldPatch (ball 0 (2*P.radius)))) ≤
            ENNReal.ofReal (B*δ^(-ε))*eLpNorm f n
              ((atlasRiemannianVolume (n:=n) p).restrict
                (C.manifoldPatch (ball 0 (2*P.radius)))) := by
  obtain ⟨C⟩ := nonempty_manifold_localBeltramiChart p hκ
  obtain ⟨P⟩ := C.nonempty_manifoldTubePatch
  exact ⟨C,P,fun ε ell hε hell hell1 =>
    P.endpointNikodymMaximal_bound hn hε hell hell1⟩

end OAI.Geometry.Nikodym
