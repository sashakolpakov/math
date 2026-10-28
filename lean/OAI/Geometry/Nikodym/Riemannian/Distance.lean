import OAI.Geometry.Nikodym.Riemannian.Smooth

noncomputable section
open Set Bundle Manifold
open scoped ContDiff

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Intrinsic Riemannian extended distance, defined using actual C¹ paths
and their metric lengths. Its topology is the original open-domain topology. -/
@[instance_reducible]
def intrinsicEMetricSpace (g : SmoothCoordinateMetric E) : EMetricSpace g.openDomain := by
  letI := g.toRiemannianBundle
  letI := g.isContinuousRiemannianBundle
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) g.openDomain

theorem intrinsic_edist (g : SmoothCoordinateMetric E) :
    letI := g.toRiemannianBundle
    ∀ x y : g.openDomain,
      @edist g.openDomain g.intrinsicEMetricSpace.toEDist x y =
        riemannianEDist 𝓘(ℝ,E) x y := by
  let := g.toRiemannianBundle
  intro x y
  rfl

theorem intrinsic_isRiemannianManifold (g : SmoothCoordinateMetric E) :
    letI := g.toRiemannianBundle
    letI := g.intrinsicEMetricSpace.toPseudoEMetricSpace
    IsRiemannianManifold 𝓘(ℝ,E) g.openDomain := by
  let := g.toRiemannianBundle
  let := g.intrinsicEMetricSpace.toPseudoEMetricSpace
  exact ⟨g.intrinsic_edist⟩

theorem norm_tangent (g : SmoothCoordinateMetric E) :
    letI := g.toRiemannianBundle
    ∀ (x : g.openDomain) (v : TangentSpace 𝓘(ℝ,E) x),
      ‖v‖ = Real.sqrt (g.inner x v v) := by
  let := g.toRiemannianBundle
  intro x v
  rw [norm_eq_sqrt_real_inner]
  rfl

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
