import OAI.Geometry.Nikodym.SpaceFormLocal
import OAI.Geometry.Nikodym.MetricNormalization
import OAI.Geometry.Nikodym.IsometryBeltrami

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter Metric
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A genuine local smooth Beltrami chart, with the metric relation as
checked data. Existence is proved below from curvature, not assumed. -/
structure LocalBeltramiChart (g : SmoothCoordinateMetric E) (κ : ℝ) (x₀ : E) where
  chart : OpenPartialHomeomorph E E
  base_mem : x₀ ∈ chart.source
  base_value : chart x₀ = 0
  source_domain : chart.source ⊆ g.domain
  smooth : ContDiffOn ℝ ∞ (chart : E → E) chart.source
  inverse_smooth : ContDiffOn ℝ ∞ (chart.symm : E → E) chart.target
  positive : ∀ x ∈ chart.source, 0 < beltramiDenominator κ (chart x)
  metric : ∀ x ∈ chart.source, ∀ u v,
    g.inner x u v = beltramiMetric κ (chart x)
      (fderiv ℝ (chart : E → E) x u) (fderiv ℝ (chart : E → E) x v)

theorem SmoothCoordinateMetric.metric_isometry_isInvertible
    (g : SmoothCoordinateMetric E) {x : E} (hx : x ∈ g.domain)
    (L : E →L[ℝ] E) (κ : ℝ) (y : E)
    (hmetric : ∀ u v, g.inner x u v = beltramiMetric κ y (L u) (L v)) :
    L.IsInvertible := by
  have hs := g.metric_isometry_surjective hx L κ y hmetric
  have hi := (LinearMap.injective_iff_surjective).mpr hs
  exact ⟨ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs),rfl⟩

/-- Local inverse germs with an actual metric identity give a single
open chart on which all identities hold. -/
theorem localBeltramiChart_of_metric_germ {g : SmoothCoordinateMetric E}
    {κ : ℝ} {x₀ : E} (φ : E → E) (hφ₀ : φ x₀ = 0)
    (hgood : ∀ᶠ y in 𝓝 x₀, y ∈ g.domain ∧ ContDiffAt ℝ ∞ φ y ∧
      0 < beltramiDenominator κ (φ y) ∧
      ∀ u v, g.inner y u v = beltramiMetric κ (φ y)
        (fderiv ℝ φ y u) (fderiv ℝ φ y v)) :
    Nonempty (LocalBeltramiChart g κ x₀) := by
  have hb := hgood.self_of_nhds
  obtain ⟨L,hL⟩ := g.metric_isometry_isInvertible hb.1 _ κ _ hb.2.2.2
  have hd : HasFDerivAt φ (L : E →L[ℝ] E) x₀ := by
    rw [hL]
    exact (hb.2.1.differentiableAt (by simp)).hasFDerivAt
  let e := hb.2.1.toOpenPartialHomeomorph φ hd (by simp)
  have he : (e : E → E) = φ := rfl
  have he0 : x₀ ∈ e.source := hb.2.1.mem_toOpenPartialHomeomorph_source hd (by simp)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let q := e.restrOpen (ball x₀ r) isOpen_ball
  have hq : (q : E → E) = φ := rfl
  have hqs : q.source = e.source ∩ ball x₀ r := e.restrOpen_source _ _
  have hg (x : E) (hx : x ∈ q.source) := hball ((hqs ▸ hx).2)
  refine ⟨{ chart := q
            base_mem := hqs.symm ▸ ⟨he0,mem_ball_self hr⟩
            base_value := hq ▸ hφ₀
            source_domain := fun x hx => (hg x hx).1
            smooth := ?_
            inverse_smooth := ?_
            positive := ?_
            metric := ?_ }⟩
  · intro x hx
    rw [hq]
    exact (hg x hx).2.1.contDiffWithinAt
  · intro y hy
    have hx := q.map_target hy
    have hh := hg (q.symm y) hx
    obtain ⟨A,hA⟩ := g.metric_isometry_isInvertible hh.1 _ κ _ hh.2.2.2
    apply ContDiffAt.contDiffWithinAt
    apply q.contDiffAt_symm hy
    · rw [hq,hA]
      exact (hh.2.1.differentiableAt (by simp)).hasFDerivAt
    · rw [hq]
      exact hh.2.1
  · intro x hx
    rw [hq]
    exact (hg x hx).2.2.1
  · intro x hx u v
    rw [hq]
    exact (hg x hx).2.2.2 u v

theorem LocalGeodesicFlow.nonempty_localBeltramiChart {g : SmoothCoordinateMetric E}
    {x₀ : E} (F : LocalGeodesicFlow g x₀) {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    (R : E ≃L[ℝ] E) (hR : ∀ u v, g.inner x₀ u v = inner ℝ (R u) (R v))
    (hx₀ : x₀ ∈ g.domain) : Nonempty (LocalBeltramiChart g κ x₀) := by
  obtain ⟨φ,ψ,hφ,hψ,hgood,hinv⟩ := F.exists_local_beltrami_maps hκ R hR hx₀
  apply localBeltramiChart_of_metric_germ φ hφ
  filter_upwards [hgood] with y hy
  exact ⟨hy.1,hy.2.1,hy.2.2.2⟩

/-- The local space-form theorem in ordinary finite-dimensional coordinates.
The flow, its smooth dependence, its inverse, and the normal metric are all
constructed from the given smooth metric. -/
theorem SmoothCoordinateMetric.nonempty_localBeltramiChart {n : ℕ}
    (g : SmoothCoordinateMetric (EuclideanSpace ℝ (Fin n))) {κ : ℝ}
    (hκ : g.HasConstantCurvature κ) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ g.domain) :
    Nonempty (LocalBeltramiChart g κ x₀) := by
  obtain ⟨R,hR⟩ := g.exists_metric_normalization hx₀
  obtain ⟨F⟩ := exists_localGeodesicFlow g hx₀
  exact F.nonempty_localBeltramiChart hκ R hR hx₀

namespace LocalBeltramiChart

variable {g : SmoothCoordinateMetric E} {κ : ℝ} {x₀ : E}
variable (C : LocalBeltramiChart g κ x₀)

theorem geodesic_image_in_line {γ v : ℝ → E} {I : Set ℝ}
    (hc : IsMetricGeodesic g γ v I) (hinside : MapsTo γ I C.chart.source)
    (hI : IsOpen I) (hconn : IsPreconnected I) {t₀ : ℝ} (h₀ : t₀ ∈ I) :
    ∃ c : E, ∀ t ∈ I, ∃ s : ℝ, C.chart (γ t) = C.chart (γ t₀) + s • c := by
  apply hc.beltrami_image_in_line (κ := κ) (Φ := C.chart) _ _ _ hI hconn h₀
  · intro t ht
    exact C.positive _ (hinside ht)
  · intro t ht
    exact ((C.smooth _ (hinside ht)).contDiffAt
      (C.chart.open_source.mem_nhds (hinside ht))).of_le (by simp)
  · intro t ht
    filter_upwards [C.chart.open_source.mem_nhds (hinside ht)] with y hy
    exact C.metric y hy

end LocalBeltramiChart
end OAI.Geometry.Nikodym
