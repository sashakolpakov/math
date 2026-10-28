import OAI.Geometry.Nikodym.SmoothConnection

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem metricKoszulVector_add_left (D : E →L[ℝ] E →L[ℝ] E) (u u' v : E) :
    metricKoszulVector D (u+u') v = metricKoszulVector D u v + metricKoszulVector D u' v := by
  apply ext_inner_right ℝ
  intro w
  simp only [inner_metricKoszulVector,inner_add_left,map_add,add_apply]
  ring

theorem metricKoszulVector_add_right (D : E →L[ℝ] E →L[ℝ] E) (u v v' : E) :
    metricKoszulVector D u (v+v') = metricKoszulVector D u v + metricKoszulVector D u v' := by
  apply ext_inner_right ℝ
  intro w
  simp only [inner_metricKoszulVector,inner_add_left,inner_add_right,map_add,add_apply]
  ring

theorem metricKoszulVector_smul_left (D : E →L[ℝ] E →L[ℝ] E) (c : ℝ) (u v : E) :
    metricKoszulVector D (c • u) v = c • metricKoszulVector D u v := by
  apply ext_inner_right ℝ
  intro w
  simp only [inner_metricKoszulVector,real_inner_smul_left,map_smul,smul_apply]
  ring

theorem metricKoszulVector_smul_right (D : E →L[ℝ] E →L[ℝ] E) (c : ℝ) (u v : E) :
    metricKoszulVector D u (c • v) = c • metricKoszulVector D u v := by
  apply ext_inner_right ℝ
  intro w
  simp only [inner_metricKoszulVector,real_inner_smul_left,inner_smul_right,map_smul,
    smul_apply]
  ring

namespace SmoothCoordinateMetric

variable (g : SmoothCoordinateMetric E)

theorem christoffel_add_left (x u u' v : E) :
    g.christoffel x (u+u') v = g.christoffel x u v + g.christoffel x u' v := by
  simp only [SmoothCoordinateMetric.christoffel,metricChristoffel,metricKoszulVector_add_left,map_add]

theorem christoffel_add_right (x u v v' : E) :
    g.christoffel x u (v+v') = g.christoffel x u v + g.christoffel x u v' := by
  simp only [SmoothCoordinateMetric.christoffel,metricChristoffel,metricKoszulVector_add_right,map_add]

theorem christoffel_smul_left (x : E) (c : ℝ) (u v : E) :
    g.christoffel x (c • u) v = c • g.christoffel x u v := by
  simp only [SmoothCoordinateMetric.christoffel,metricChristoffel,metricKoszulVector_smul_left,map_smul]

theorem christoffel_smul_right (x : E) (c : ℝ) (u v : E) :
    g.christoffel x u (c • v) = c • g.christoffel x u v := by
  simp only [SmoothCoordinateMetric.christoffel,metricChristoffel,metricKoszulVector_smul_right,map_smul]

@[simp] theorem christoffel_zero_left (x v : E) : g.christoffel x 0 v = 0 := by
  simpa only [zero_smul] using g.christoffel_smul_left x 0 (0 : E) v

@[simp] theorem christoffel_zero_right (x u : E) : g.christoffel x u 0 = 0 := by
  simpa only [zero_smul] using g.christoffel_smul_right x 0 u (0 : E)

theorem christoffel_smul_self (x v : E) (c : ℝ) :
    g.christoffel x (c • v) (c • v) = c^2 • g.christoffel x v v := by
  rw [g.christoffel_smul_left,g.christoffel_smul_right,smul_smul,pow_two]

/-- Curvature of the constructed Levi-Civita connection in commuting
coordinates, with convention R(u,v)w = ∇u∇v w − ∇v∇u w. -/
def curvature (x u v w : E) : E :=
  fderiv ℝ (fun y => g.christoffel y v w) x u -
  fderiv ℝ (fun y => g.christoffel y u w) x v +
  g.christoffel x u (g.christoffel x v w) -
  g.christoffel x v (g.christoffel x u w)

/-- The ordinary constant sectional curvature tensor identity for a
positive smooth metric. No model chart is part of this hypothesis. -/
def HasConstantCurvature (κ : ℝ) : Prop :=
  ∀ x ∈ g.domain, ∀ u v w,
    g.curvature x u v w = κ • (g.inner x v w • u - g.inner x u w • v)

theorem curvature_swap (x u v w : E) : g.curvature x v u w = -g.curvature x u v w := by
  unfold SmoothCoordinateMetric.curvature
  abel

@[simp] theorem curvature_self (x u w : E) : g.curvature x u u w = 0 := by
  simp [SmoothCoordinateMetric.curvature]

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
