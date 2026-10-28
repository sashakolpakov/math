import OAI.Geometry.Riemannian.LengthSpace
import OAI.Geometry.Nikodym.Riemannian.MetricSpace
import OAI.Geometry.Nikodym.DistanceHoles

noncomputable section
open Set Bundle Manifold
open scoped ENNReal

namespace OAI.Geometry.Nikodym.IntrinsicDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual finite intrinsic metric on a convex bounded-metric coordinate domain
has the approximate intermediate-point property required for distance-level porosity. -/
theorem hasApproximateIntermediatePoints (g : SmoothCoordinateMetric E)
    (hconv : Convex ℝ g.domain) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ x ∈ g.domain, ∀ v, g.inner x v v ≤ C * ‖v‖ ^ 2) :
    letI := IntrinsicDomain.metricSpaceOfConvex g hconv hC hupper
    HasApproximateIntermediatePoints (IntrinsicDomain g) := by
  let : ChartedSpace E (IntrinsicDomain g) :=
    inferInstanceAs (ChartedSpace E g.openDomain)
  let : RiemannianBundle (fun x : IntrinsicDomain g => TangentSpace 𝓘(ℝ,E) x) :=
    g.toRiemannianBundle
  let : IsRiemannianManifold 𝓘(ℝ,E) (IntrinsicDomain g) :=
    g.intrinsic_isRiemannianManifold
  have hi (x y : IntrinsicDomain g) (s ε : ℝ≥0∞)
      (hs : s ≤ edist x y) (hε : 0 < ε) :
      ∃ z : IntrinsicDomain g, edist x z = s ∧
        edist x z + edist z y < edist x y + ε :=
    @OAI.Geometry.Riemannian.exists_intermediate_edist E _ _ E _ 𝓘(ℝ,E)
      (IntrinsicDomain g) g.intrinsicEMetricSpace.toPseudoEMetricSpace
      (inferInstanceAs (ChartedSpace E g.openDomain)) g.toRiemannianBundle
      g.intrinsic_isRiemannianManifold x y
      (IntrinsicDomain.edist_ne_top_of_convex g hconv hC hupper x y) s ε hs hε
  let := IntrinsicDomain.metricSpaceOfConvex g hconv hC hupper
  have hed (a b : IntrinsicDomain g) : edist a b = ENNReal.ofReal (dist a b) :=
    @edist_dist _ (IntrinsicDomain.metricSpaceOfConvex g hconv hC hupper).toPseudoMetricSpace a b
  intro x y s ε hs hsd hε
  have hse : ENNReal.ofReal s ≤ edist x y := by
    rw [hed]
    exact ENNReal.ofReal_le_ofReal hsd.le
  obtain ⟨z, heq, hsum⟩ := hi x y (ENNReal.ofReal s) (ENNReal.ofReal ε)
    hse (ENNReal.ofReal_pos.mpr hε)
  have heq' : dist x z = s := by
    rw [hed] at heq
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg hs.le).mp heq
  have hsum' : dist x z + dist z y < dist x y + ε := by
    simp only [hed] at hsum
    rw [← ENNReal.ofReal_add dist_nonneg dist_nonneg,
      ← ENNReal.ofReal_add dist_nonneg hε.le] at hsum
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  refine ⟨z, heq', ?_⟩
  linarith

end OAI.Geometry.Nikodym.IntrinsicDomain
