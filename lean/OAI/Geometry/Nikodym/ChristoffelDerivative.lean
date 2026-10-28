import OAI.Geometry.Nikodym.MetricCurvature

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

def christoffelLinear (x u : E) : E →L[ℝ] E :=
  (show E →ₗ[ℝ] E from
    { toFun := g.christoffel x u
      map_add' := g.christoffel_add_right x u
      map_smul' := fun c v => g.christoffel_smul_right x c u v }).toContinuousLinearMap

@[simp] theorem christoffelLinear_apply (x u v : E) :
    g.christoffelLinear x u v = g.christoffel x u v := rfl

def christoffelBilinear (x : E) : E →L[ℝ] E →L[ℝ] E :=
  (show E →ₗ[ℝ] E →L[ℝ] E from
    { toFun := g.christoffelLinear x
      map_add' := by
        intro u v
        ext w
        exact g.christoffel_add_left x u v w
      map_smul' := by
        intro c u
        ext w
        exact g.christoffel_smul_left x c u w }).toContinuousLinearMap

@[simp] theorem christoffelBilinear_apply (x u v : E) :
    g.christoffelBilinear x u v = g.christoffel x u v := rfl

theorem contDiffAt_christoffelBilinear {x : E} (hx : x ∈ g.domain) :
    ContDiffAt ℝ ∞ g.christoffelBilinear x := by
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro u
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  exact ((g.contDiffAt_christoffel hx u v).comp x
    (contDiffAt_id.prodMk (contDiffAt_const.prodMk contDiffAt_const))).contDiffWithinAt

theorem fderiv_christoffel_apply {x : E} (hx : x ∈ g.domain) (w u v : E) :
    fderiv ℝ g.christoffelBilinear x w u v =
      fderiv ℝ (fun y => g.christoffel y u v) x w := by
  have hd := (g.contDiffAt_christoffelBilinear hx).differentiableAt (by simp)
  have hh := ((hd.hasFDerivAt.clm_apply (hasFDerivAt_const u x)).clm_apply
    (hasFDerivAt_const v x)).fderiv
  have hh' := congrArg (fun L : E →L[ℝ] E => L w) hh
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    zero_apply,ContinuousLinearMap.flip_apply,map_zero,zero_add,
    SmoothCoordinateMetric.christoffelBilinear_apply] using hh'.symm

/-- Ordinary derivative of the actual Christoffel expression, including
all three moving arguments. -/
theorem hasDerivAt_christoffel {γ U V : ℝ → E} {t : ℝ} {w u v : E}
    (ht : γ t ∈ g.domain) (hγ : HasDerivAt γ w t)
    (hU : HasDerivAt U u t) (hV : HasDerivAt V v t) :
    HasDerivAt (fun s => g.christoffel (γ s) (U s) (V s))
      (fderiv ℝ (fun y => g.christoffel y (U t) (V t)) (γ t) w +
        g.christoffel (γ t) u (V t) + g.christoffel (γ t) (U t) v) t := by
  have hd := (g.contDiffAt_christoffelBilinear ht).differentiableAt (by simp)
  have hh := (((hd.hasFDerivAt.comp_hasDerivAt t hγ).clm_apply hU).clm_apply hV)
  convert hh using 1 <;>
    simp only [Function.comp_def,SmoothCoordinateMetric.christoffelBilinear_apply,add_apply,
      g.fderiv_christoffel_apply ht]

theorem fderiv_christoffel_symmetric {x : E} (hx : x ∈ g.domain) (w u v : E) :
    fderiv ℝ (fun y => g.christoffel y u v) x w =
      fderiv ℝ (fun y => g.christoffel y v u) x w := by
  have he : (fun y => g.christoffel y u v) =ᶠ[𝓝 x] (fun y => g.christoffel y v u) := by
    filter_upwards [g.isOpen_domain.mem_nhds hx] with y hy
    exact g.christoffel_symmetric hy u v
  exact congrArg (fun L : E →L[ℝ] E => L w) he.fderiv_eq

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
