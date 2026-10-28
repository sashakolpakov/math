import OAI.Geometry.Nikodym.GeodesicLinearization
import OAI.Geometry.Nikodym.Jacobi.Speed

noncomputable section
namespace OAI.Geometry.Nikodym.LocalGeodesicFlow

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {x₀ : E} (F : LocalGeodesicFlow g x₀)

def positionVariation (w u : E) (t : ℝ) : E := (F.stateVariation w u t).1
def velocityVariation (w u : E) (t : ℝ) : E := (F.stateVariation w u t).2

def covariantVariation (w u : E) : ℝ → E :=
  g.variationVelocity (fun t => F.position (w,t)) (fun t => F.velocity (w,t))
    (F.positionVariation w u) (F.velocityVariation w u)

theorem variation_coordinate_derivatives {w : E} (hw : w ∈ F.velocities) (u : E)
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    HasDerivAt (F.positionVariation w u) (F.velocityVariation w u t) t ∧
    HasDerivAt (F.velocityVariation w u)
      (-(fderiv ℝ (fun x => g.christoffel x (F.velocity (w,t)) (F.velocity (w,t)))
          (F.position (w,t)) (F.positionVariation w u t) +
        g.christoffel (F.position (w,t)) (F.velocityVariation w u t) (F.velocity (w,t)) +
        g.christoffel (F.position (w,t)) (F.velocity (w,t)) (F.velocityVariation w u t))) t := by
  have hd := F.stateVariation_derivative hw u ht
  have he := g.fderiv_geodesicSpray_apply ((F.geodesic w hw).regular t ht)
    (F.state (w,t)).2 (F.stateVariation w u t).1 (F.stateVariation w u t).2
  change fderiv ℝ g.geodesicSpray (F.state (w,t)) (F.stateVariation w u t) = _ at he
  rw [he] at hd
  exact ⟨hd.fst,hd.snd⟩

theorem spaceFormJacobiField {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    {w : E} (hw : w ∈ F.velocities) (u : E) :
    IsSpaceFormJacobiField g κ (fun t => F.position (w,t)) (fun t => F.velocity (w,t))
      (F.positionVariation w u) (F.covariantVariation w u) (Ioo (-F.radius) F.radius) :=
  (F.geodesic w hw).spaceFormJacobiField_of_linearized hκ
    (fun _ ht => (F.variation_coordinate_derivatives hw u ht).1)
    (fun _ ht => (F.variation_coordinate_derivatives hw u ht).2)

theorem positionVariation_initial {w : E} (hw : w ∈ F.velocities) (u : E) :
    F.positionVariation w u 0 = 0 := congrArg Prod.fst (F.stateVariation_initial hw u)

theorem covariantVariation_initial {w : E} (hw : w ∈ F.velocities) (u : E) :
    F.covariantVariation w u 0 = u := by
  simp only [LocalGeodesicFlow.covariantVariation,OAI.Geometry.Nikodym.SmoothCoordinateMetric.variationVelocity,
    LocalGeodesicFlow.positionVariation,LocalGeodesicFlow.velocityVariation,F.stateVariation_initial hw u,
    OAI.Geometry.Nikodym.SmoothCoordinateMetric.christoffel_zero_right,add_zero]

theorem positionVariation_eq_fderiv {w : E} (hw : w ∈ F.velocities) (u : E)
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    F.positionVariation w u t = fderiv ℝ (fun v => F.position (v,t)) w u := by
  have hd := ((F.contDiffAt_state_slice hw ht).differentiableAt (by simp)).hasFDerivAt.fst
  exact (congrArg (fun L : E →L[ℝ] E => L u) hd.fderiv).symm

/-- The exact differential metric of the genuine geodesic endpoint map
in a constant-curvature metric, at every nonzero initial velocity. -/
theorem endpoint_metric {κ : ℝ} (hκ : g.HasConstantCurvature κ)
    {w : E} (hw : w ∈ F.velocities) (hw0 : w ≠ 0) (u₁ u₂ : E)
    {t : ℝ} (ht : t ∈ Ioo (-F.radius) F.radius) :
    let c := Real.sqrt (g.inner x₀ w w)
    g.inner (F.position (w,t))
        (fderiv ℝ (fun v => F.position (v,t)) w u₁)
        (fderiv ℝ (fun v => F.position (v,t)) w u₂) =
      t^2 * (g.inner x₀ u₁ w * g.inner x₀ u₂ w / c^2) +
      (curvatureSin κ (c*t) / c)^2 *
        (g.inner x₀ u₁ u₂ - g.inner x₀ u₁ w * g.inner x₀ u₂ w / c^2) := by
  let c := Real.sqrt (g.inner x₀ w w)
  have h0 : (0 : ℝ) ∈ Ioo (-F.radius) F.radius := ⟨neg_neg_of_pos F.radius_pos,F.radius_pos⟩
  have hx : x₀ ∈ g.domain := by
    simpa only [F.initial w hw] using (F.geodesic w hw).regular 0 h0
  have hp : 0 < g.inner x₀ w w := g.positive x₀ hx w hw0
  have hc : 0 < c := Real.sqrt_pos.mpr hp
  have hc2 : c^2 = g.inner x₀ w w := Real.sq_sqrt hp.le
  have hs (s : ℝ) (hss : s ∈ Ioo (-F.radius) F.radius) :
      g.inner (F.position (w,s)) (F.velocity (w,s)) (F.velocity (w,s)) = c^2 := by
    rw [hc2]
    simpa only [LocalGeodesicFlow.position,LocalGeodesicFlow.velocity,F.initial w hw] using
      (F.geodesic w hw).speed_sq_eq (convex_Ioo _ _) h0 hss
  have he := (F.spaceFormJacobiField hκ hw u₁).normal_metric_speed
    (F.spaceFormJacobiField hκ hw u₂) (F.geodesic w hw) (convex_Ioo _ _) h0 hc hs
    (F.positionVariation_initial hw u₁) (F.positionVariation_initial hw u₂) ht
  simpa only [F.positionVariation_eq_fderiv hw u₁ ht,F.positionVariation_eq_fderiv hw u₂ ht,
    F.covariantVariation_initial hw u₁,F.covariantVariation_initial hw u₂,
    LocalGeodesicFlow.position,LocalGeodesicFlow.velocity,F.initial w hw] using he

end OAI.Geometry.Nikodym.LocalGeodesicFlow
