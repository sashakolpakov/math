import OAI.Geometry.Nikodym.GeodesicEstimate
import OAI.Geometry.Nikodym.GeodesicDimension
import OAI.Geometry.Nikodym.Abstract.Sectional

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Metric
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym

open OAI.Geometry.Nikodym

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

/-- The maximal estimate for all genuine fixed-length geodesic images
in the compact core, using ambient Riemannian tubes and volume. -/
def LocalGeodesicNikodymEstimate (P : OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch C) : Prop :=
  ∀ ε ell : ℝ, 0 < ε → 0 < ell → ell ≤ 1/4 →
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ P.width → ∀ f : M → ℂ,
      MemLp f n ((atlasRiemannianVolume (n:=n) p).restrict
        (C.manifoldPatch (ball 0 (2*P.radius)))) →
      MemLp (P.geodesicNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict
          (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
      eLpNorm (P.geodesicNikodymMaximal ell δ f) n
        ((atlasRiemannianVolume (n:=n) p).restrict
          (C.manifoldPatch (ball 0 (2*P.radius)))) ≤
      ENNReal.ofReal (B*δ^(-ε))*eLpNorm f n
        ((atlasRiemannianVolume (n:=n) p).restrict
          (C.manifoldPatch (ball 0 (2*P.radius))))

/-- The dimension conclusion with actual Hausdorff intersection measure
and actual Riemannian geodesic length, without selecting a parameterization. -/
def LocalGeodesicNikodymDimension (P : OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch C) : Prop :=
  ∀ (A Ω : Set M) (ell η : ℝ), 0 < ell → ell ≤ 1/4 → 0 < η →
    MeasurableSet Ω → 0 < atlasRiemannianVolume (n:=n) p Ω →
    (∀ x ∈ Ω, ∃ J : Set M, P.IsLocalGeodesicImage ell J ∧ x ∈ J ∧
      ENNReal.ofReal η ≤ Measure.hausdorffMeasure 1 (A ∩ J)) →
    dimH (A ∩ C.manifoldPatch (ball 0 (2*P.radius))) = n

/-- Both local constant-sectional-curvature Nikodym conclusions from
`sections/further_geometry.tex`. The chart and quantitative patch are
constructed, and the neighborhood is open and relatively compact.
No straightening, volume-comparison, measurability, or local-smoothing
hypothesis is required. -/
theorem local_geodesic_nikodym (hn : 2 ≤ n) (p : M) {κ : ℝ}
    (hκ : (abstractChartMetric (E:=Space n) p).HasConstantSectionalCurvature κ) :
    ∃ (C : LocalBeltramiChart (abstractChartMetric (E:=Space n) p) κ
        (extChartAt 𝓘(ℝ,Space n) p p)) (P : OAI.Geometry.Nikodym.LocalBeltramiChart.ManifoldTubePatch C),
      IsOpen (C.manifoldPatch (ball 0 (2*P.radius))) ∧
      p ∈ C.manifoldPatch (ball 0 (2*P.radius)) ∧
      IsCompact (closure (C.manifoldPatch (ball 0 (2*P.radius)))) ∧
      LocalGeodesicNikodymEstimate P ∧ LocalGeodesicNikodymDimension P := by
  obtain ⟨C⟩ := nonempty_manifold_localBeltramiChart p hκ
  obtain ⟨P⟩ := C.nonempty_manifoldTubePatch
  have hi : ContinuousOn C.manifoldInverse (closedBall (0 : Space n) (2*P.radius)) := by
    apply C.manifoldChart.symm.continuousOn.congr_mono
      (fun y hy => C.manifoldInverse_eq (P.target hy))
    change closedBall (0 : Space n) (2*P.radius) ⊆ C.manifoldChart.target
    rw [C.manifoldChart_target]
    exact P.target
  have hcompact : IsCompact (C.manifoldPatch (closedBall (0 : Space n) (2*P.radius))) := by
    rw [←C.manifoldInverse_image P.target]
    exact (isCompact_closedBall (0 : Space n) (2*P.radius)).image_of_continuousOn hi
  have hclosure : IsCompact (closure (C.manifoldPatch (ball 0 (2*P.radius)))) :=
    hcompact.of_isClosed_subset isClosed_closure
      (closure_minimal (C.manifoldPatch_mono ball_subset_closedBall) hcompact.isClosed)
  have hp : p ∈ C.manifoldPatch (ball 0 (2*P.radius)) :=
    C.manifoldPatch_mono (ball_subset_ball (by linarith [P.radius_pos])) P.base_mem
  refine ⟨C,P,C.isOpen_manifoldPatch isOpen_ball,hp,hclosure,?_,?_⟩
  · exact fun ε ell hε hell hell1 => P.geodesicNikodymMaximal_bound hn hε hell hell1
  · exact fun A Ω ell η hell hell1 hη hΩ hΩpos hinc =>
      P.geodesic_incidence_dimension hn hell hell1 hη hΩ hΩpos hinc

end OAI.Geometry.Nikodym
