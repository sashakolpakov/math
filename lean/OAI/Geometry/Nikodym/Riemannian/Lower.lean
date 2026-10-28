import OAI.Geometry.Nikodym.Riemannian.Norm
import OAI.Geometry.Nikodym.OpenMFDeriv
import OAI.Geometry.Riemannian.EDistMap

noncomputable section
open Set Bundle Manifold
open scoped ContDiff ENNReal

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem norm_mfderiv_coordinate_le (g : SmoothCoordinateMetric E) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ g.domain, ∀ v, c * ‖v‖^2 ≤ g.inner x v v) :
    letI := g.toRiemannianBundle
    ∀ x : g.openDomain,
      ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : g.openDomain → E) x‖ ≤
        1 / Real.sqrt c := by
  let := g.toRiemannianBundle
  intro x
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  calc
    ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (Subtype.val : g.openDomain → E) x v‖ =
        ‖(show E from v)‖ := by
      rw [opens_mfderiv_subtype_val]
      exact norm_tangentSpace_vectorSpace
    _ ≤ (1 / Real.sqrt c) * ‖v‖ := g.coordinate_norm_le hc hcoer x v

/-- Coercivity gives a lower bound for the true path distance, including
paths that wander through the whole coordinate domain. -/
theorem edist_coordinate_le_riemannianEDist (g : SmoothCoordinateMetric E)
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x ∈ g.domain, ∀ v, c * ‖v‖^2 ≤ g.inner x v v) :
    letI := g.toRiemannianBundle
    ∀ x y : g.openDomain, edist (x:E) (y:E) ≤
      ENNReal.ofReal (1 / Real.sqrt c) * riemannianEDist 𝓘(ℝ,E) x y := by
  let := g.toRiemannianBundle
  let K : NNReal := ⟨1 / Real.sqrt c,by positivity⟩
  have hK : 0 < K := by change 0 < 1 / Real.sqrt c; positivity
  have hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) 1 (Subtype.val : g.openDomain → E) :=
    contMDiff_subtype_val
  intro x y
  have h := OAI.Geometry.Riemannian.edist_map_le_riemannianEDist hf hK
    (g.norm_mfderiv_coordinate_le hc hcoer) x y
  change edist (x:E) (y:E) ≤ ENNReal.ofReal (K : ℝ) * riemannianEDist 𝓘(ℝ,E) x y
  simpa only [ENNReal.ofReal_coe_nnreal] using h

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
