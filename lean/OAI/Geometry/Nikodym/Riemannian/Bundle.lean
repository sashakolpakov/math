import OAI.Geometry.Nikodym.Riemannian.Coercivity
import Mathlib.Geometry.Manifold.Riemannian.Basic

noncomputable section
open Set Metric Bundle Manifold Bornology
open scoped RealInnerProductSpace ContDiff

namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The coordinate domain as an open submanifold of its model space. -/
def openDomain (g : SmoothCoordinateMetric E) : TopologicalSpace.Opens E :=
  ⟨g.domain,g.isOpen_domain⟩

/-- Continuous bilinear form associated to the actual coefficient operator. -/
def metricForm (g : SmoothCoordinateMetric E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ (E := E)).comp (g.coefficient x)

omit [FiniteDimensional ℝ E] in
@[simp] theorem metricForm_apply (g : SmoothCoordinateMetric E) (x u v : E) :
    g.metricForm x u v = g.inner x u v := rfl

/-- Pointwise metric on the true tangent spaces of the open domain.
The bundle construction preserves their existing topology. -/
def toRiemannianMetric (g : SmoothCoordinateMetric E) :
    RiemannianMetric (fun x : g.openDomain => TangentSpace 𝓘(ℝ,E) x) where
  inner x := by
    change E →L[ℝ] E →L[ℝ] ℝ
    exact g.metricForm x
  symm x u v := by
    change g.inner x u v = g.inner x v u
    exact (g.symmetric x x.property u v).trans (real_inner_comm _ _)
  pos x u hu := by
    change 0 < g.inner x u u
    exact g.positive x x.property u hu
  continuousAt x := by
    change ContinuousAt (fun u : E => g.inner x u u) 0
    unfold SmoothCoordinateMetric.inner
    exact ((g.coefficient x).continuous.inner continuous_id).continuousAt
  isVonNBounded x := by
    change IsVonNBounded ℝ {u : E | g.inner x u u < 1}
    exact g.unitBall_isVonNBounded x.property

@[instance_reducible]
def toRiemannianBundle (g : SmoothCoordinateMetric E) :
    RiemannianBundle (fun x : g.openDomain => TangentSpace 𝓘(ℝ,E) x) :=
  ⟨g.toRiemannianMetric⟩

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
