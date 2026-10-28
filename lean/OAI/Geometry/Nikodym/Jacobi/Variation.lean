import OAI.Geometry.Nikodym.ChristoffelDerivative
import OAI.Geometry.Nikodym.MetricGeodesic

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

/-- The covariant derivative of a variation field, with its ordinary
coordinate derivative recorded explicitly. -/
def variationVelocity (γ v J U : ℝ → E) (t : ℝ) : E :=
  U t + g.christoffel (γ t) (v t) (J t)

/-- The linearized coordinate geodesic equation implies the actual
covariant Jacobi equation. All curvature terms use the connection
constructed from the given metric. -/
theorem hasDerivAt_variationVelocity {γ v J U : ℝ → E} {t : ℝ}
    (ht : γ t ∈ g.domain)
    (hγ : HasDerivAt γ (v t) t)
    (hv : HasDerivAt v (-g.christoffel (γ t) (v t) (v t)) t)
    (hJ : HasDerivAt J (U t) t)
    (hU : HasDerivAt U
      (-(fderiv ℝ (fun x => g.christoffel x (v t) (v t)) (γ t) (J t) +
        g.christoffel (γ t) (U t) (v t) + g.christoffel (γ t) (v t) (U t))) t) :
    HasDerivAt (g.variationVelocity γ v J U)
      (-g.curvature (γ t) (J t) (v t) (v t) -
        g.christoffel (γ t) (v t) (g.variationVelocity γ v J U t)) t := by
  have hh := hU.add (g.hasDerivAt_christoffel ht hγ hv hJ)
  change HasDerivAt (fun s => U s + g.christoffel (γ s) (v s) (J s)) _ t
  convert hh using 1
  have hn (a b : E) : g.christoffel (γ t) (-a) b = -g.christoffel (γ t) a b := by
    simpa only [neg_one_smul] using g.christoffel_smul_left (γ t) (-1) a b
  simp only [SmoothCoordinateMetric.curvature,SmoothCoordinateMetric.variationVelocity,g.christoffel_add_right,hn]
  rw [g.christoffel_symmetric ht (U t) (v t),
    g.christoffel_symmetric ht (g.christoffel (γ t) (v t) (v t)) (J t),
    g.christoffel_symmetric ht (J t) (v t),
    g.fderiv_christoffel_symmetric ht (v t) (v t) (J t)]
  abel

theorem hasDerivAt_variationVelocity_spaceForm {κ : ℝ}
    (hκ : g.HasConstantCurvature κ) {γ v J U : ℝ → E} {t : ℝ}
    (ht : γ t ∈ g.domain)
    (hγ : HasDerivAt γ (v t) t)
    (hv : HasDerivAt v (-g.christoffel (γ t) (v t) (v t)) t)
    (hJ : HasDerivAt J (U t) t)
    (hU : HasDerivAt U
      (-(fderiv ℝ (fun x => g.christoffel x (v t) (v t)) (γ t) (J t) +
        g.christoffel (γ t) (U t) (v t) + g.christoffel (γ t) (v t) (U t))) t) :
    HasDerivAt (g.variationVelocity γ v J U)
      (-(κ • (g.inner (γ t) (v t) (v t) • J t -
          g.inner (γ t) (J t) (v t) • v t)) -
        g.christoffel (γ t) (v t) (g.variationVelocity γ v J U t)) t := by
  simpa only [hκ (γ t) ht (J t) (v t) (v t)] using
    g.hasDerivAt_variationVelocity ht hγ hv hJ hU

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
