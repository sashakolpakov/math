import OAI.Geometry.Nikodym.Sectional.CurvatureAlgebra

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

omit [FiniteDimensional ℝ E] in
theorem inner_add_first (x a b c : E) :
    g.inner x (a+b) c = g.inner x a c + g.inner x b c := by
  simp [SmoothCoordinateMetric.inner,map_add,inner_add_left]

omit [FiniteDimensional ℝ E] in
theorem inner_add_second (x a b c : E) :
    g.inner x a (b+c) = g.inner x a b + g.inner x a c := by
  simp [SmoothCoordinateMetric.inner,inner_add_right]

omit [FiniteDimensional ℝ E] in
theorem inner_sub_first (x a b c : E) :
    g.inner x (a-b) c = g.inner x a c - g.inner x b c := by
  simp [SmoothCoordinateMetric.inner,map_sub,inner_sub_left]

omit [FiniteDimensional ℝ E] in
theorem inner_sub_second (x a b c : E) :
    g.inner x a (b-c) = g.inner x a b - g.inner x a c := by
  simp [SmoothCoordinateMetric.inner,inner_sub_right]

omit [FiniteDimensional ℝ E] in
theorem inner_smul_first (x : E) (c : ℝ) (a b : E) :
    g.inner x (c • a) b = c * g.inner x a b := by
  simp [SmoothCoordinateMetric.inner,map_smul,real_inner_smul_left]

omit [FiniteDimensional ℝ E] in
theorem inner_smul_second (x : E) (c : ℝ) (a b : E) :
    g.inner x a (c • b) = c * g.inner x a b := by
  simp [SmoothCoordinateMetric.inner,inner_smul_right]

omit [FiniteDimensional ℝ E] in
theorem inner_symmetric {x : E} (hx : x ∈ g.domain) (a b : E) :
    g.inner x a b = g.inner x b a :=
  (g.symmetric x hx a b).trans (real_inner_comm _ _)

omit [FiniteDimensional ℝ E] in
@[simp] theorem inner_zero_first (x a : E) : g.inner x 0 a = 0 := by simp [SmoothCoordinateMetric.inner]
omit [FiniteDimensional ℝ E] in
@[simp] theorem inner_zero_second (x a : E) : g.inner x a 0 = 0 := by simp [SmoothCoordinateMetric.inner]

omit [FiniteDimensional ℝ E] in
theorem inner_neg_first (x a b : E) : g.inner x (-a) b = -g.inner x a b := by
  simp [SmoothCoordinateMetric.inner]

theorem curvature_zero_first {x : E} (hx : x ∈ g.domain) (v w : E) :
    g.curvature x 0 v w = 0 := by
  simpa only [zero_smul] using g.curvature_smul_first hx 0 (0:E) v w

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
