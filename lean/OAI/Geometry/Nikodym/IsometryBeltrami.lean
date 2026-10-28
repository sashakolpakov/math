import OAI.Geometry.Nikodym.IsometryGeodesic
import OAI.Geometry.Nikodym.Beltrami.ConstructedConnection
import OAI.Geometry.Nikodym.Beltrami.Geodesic

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem SmoothCoordinateMetric.metric_isometry_surjective
    (g : SmoothCoordinateMetric E) {x : E} (hx : x ∈ g.domain)
    (L : E →L[ℝ] E) (κ : ℝ) (y : E)
    (hmetric : ∀ u v, g.inner x u v = beltramiMetric κ y (L u) (L v)) :
    Function.Surjective L := by
  have hi : Function.Injective L := by
    intro u v huv
    apply sub_eq_zero.mp
    by_contra hn
    have hp := g.positive x hx (u-v) hn
    have he := hmetric (u-v) (u-v)
    simp only [map_sub,huv,sub_self,beltramiMetric,inner_zero_right,mul_zero,sub_self,zero_div] at he
    exact hp.ne' he
  exact (LinearMap.injective_iff_surjective).mp hi

/-- Actual metric geodesics become geodesics of the explicit Beltrami
connection under a verified metric pullback. Surjectivity is derived from
positive definiteness, not assumed. -/
theorem IsMetricGeodesic.map_beltrami
    {g : SmoothCoordinateMetric E} {γ v : ℝ → E} {I : Set ℝ}
    (hc : IsMetricGeodesic g γ v I) {κ : ℝ} {Φ : E → E}
    (hdom : ∀ t ∈ I, 0 < beltramiDenominator κ (Φ (γ t)))
    (hΦ : ∀ t ∈ I, ContDiffAt ℝ 2 Φ (γ t))
    (hmetric : ∀ t ∈ I, ∀ᶠ y in 𝓝 (γ t), ∀ u w,
      g.inner y u w = beltramiMetric κ (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y w)) :
    IsBeltramiGeodesic κ (fun t => Φ (γ t))
      (fun t => fderiv ℝ Φ (γ t) (v t)) I := by
  have hs : ∀ t ∈ I, Function.Surjective (fderiv ℝ Φ (γ t)) := by
    intro t ht
    exact g.metric_isometry_surjective (hc.regular t ht) _ κ _
      (hmetric t ht).self_of_nhds
  have hm : ∀ t ∈ I, ∀ᶠ y in 𝓝 (γ t), ∀ u w,
      g.inner y u w = (beltramiSmoothMetric κ).inner (Φ y)
        (fderiv ℝ Φ y u) (fderiv ℝ Φ y w) := by
    simpa only [beltramiSmoothMetric_inner] using hmetric
  have hc' := hc.map_local_isometry (h := beltramiSmoothMetric κ) hdom hΦ hs hm
  refine ⟨hc'.position_derivative,?_,hdom⟩
  intro t ht
  simpa only [beltramiSmoothMetric_christoffel (hdom t ht)] using
    hc'.velocity_derivative t ht

/-- Straightening is a conclusion of metric compatibility and the actual
geodesic equation, not an additional hypothesis on the chart. -/
theorem IsMetricGeodesic.beltrami_image_in_line
    {g : SmoothCoordinateMetric E} {γ v : ℝ → E} {I : Set ℝ}
    (hc : IsMetricGeodesic g γ v I) {κ : ℝ} {Φ : E → E}
    (hdom : ∀ t ∈ I, 0 < beltramiDenominator κ (Φ (γ t)))
    (hΦ : ∀ t ∈ I, ContDiffAt ℝ 2 Φ (γ t))
    (hmetric : ∀ t ∈ I, ∀ᶠ y in 𝓝 (γ t), ∀ u w,
      g.inner y u w = beltramiMetric κ (Φ y) (fderiv ℝ Φ y u) (fderiv ℝ Φ y w))
    (hI : IsOpen I) (hconn : IsPreconnected I) {t₀ : ℝ} (h₀ : t₀ ∈ I) :
    ∃ c : E, ∀ t ∈ I, ∃ s : ℝ, Φ (γ t) = Φ (γ t₀) + s • c :=
  (hc.map_beltrami hdom hΦ hmetric).image_in_line hI hconn h₀

end OAI.Geometry.Nikodym
