import OAI.Geometry.Nikodym.ChristoffelDerivative

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

/-- The linearized spray is obtained by differentiating the constructed
Christoffel formula, rather than imposed as a geodesic-flow axiom. -/
theorem fderiv_geodesicSpray_apply {x : E} (hx : x ∈ g.domain) (v w u : E) :
    fderiv ℝ g.geodesicSpray (x,v) (w,u) =
      (u,-(fderiv ℝ (fun y => g.christoffel y v v) x w +
        g.christoffel x u v + g.christoffel x v u)) := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • w) w 0 := by
    convert (hasDerivAt_const (0 : ℝ) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const w) using 1
    · rfl
    · simp
  have hv : HasDerivAt (fun t : ℝ => v + t • u) u 0 := by
    convert (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1
    · rfl
    · simp
  have hc := g.hasDerivAt_christoffel (by simpa using hx) hγ hv hv
  have hh := hv.prodMk hc.neg
  have hs := ((g.contDiffAt_geodesicSpray (p := (x,v)) hx).differentiableAt (by simp)).hasFDerivAt
  have hs' : HasFDerivAt g.geodesicSpray (fderiv ℝ g.geodesicSpray (x,v))
      (x + (0 : ℝ) • w,v + (0 : ℝ) • u) := by simpa only [zero_smul,add_zero] using hs
  have hd := hs'.comp_hasDerivAt 0 (hγ.prodMk hv)
  have hh' : HasDerivAt (fun t : ℝ => g.geodesicSpray (x+t•w,v+t•u))
      (u,-(fderiv ℝ (fun y => g.christoffel y v v) x w +
        g.christoffel x u v + g.christoffel x v u)) 0 := by
    convert hh using 1
    · rfl
    · simp only [zero_smul,add_zero]
  exact hd.unique hh'

theorem fderiv_geodesicSpray_zero {x : E} (hx : x ∈ g.domain) (w u : E) :
    fderiv ℝ g.geodesicSpray (x,0) (w,u) = (u,0) := by
  simpa only [SmoothCoordinateMetric.christoffel_zero_left,SmoothCoordinateMetric.christoffel_zero_right,fderiv_const_apply,
    zero_apply,add_zero,neg_zero] using
      g.fderiv_geodesicSpray_apply hx 0 w u

theorem hasFDerivAt_geodesicSpray_zero {x : E} (hx : x ∈ g.domain) :
    HasFDerivAt g.geodesicSpray
      ((ContinuousLinearMap.snd ℝ E E).prod (0 : (E × E) →L[ℝ] E)) (x,0) := by
  convert ((g.contDiffAt_geodesicSpray (p := (x,0)) hx).differentiableAt (by simp)).hasFDerivAt using 1
  apply ContinuousLinearMap.ext
  intro p
  exact (g.fderiv_geodesicSpray_zero hx p.1 p.2).symm

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
