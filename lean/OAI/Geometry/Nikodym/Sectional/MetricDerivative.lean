import OAI.Geometry.Nikodym.Sectional.CurvatureAlgebra
import OAI.Geometry.Nikodym.ParallelMetric

noncomputable section
namespace OAI.Geometry.Nikodym.SmoothCoordinateMetric

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

private theorem hasDerivAt_apply_fixed
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {A : ℝ → V →L[ℝ] W} {A' : V →L[ℝ] W} {t : ℝ}
    (hA : HasDerivAt A A' t) (v : V) :
    HasDerivAt (fun s => A s v) (A' v) t := by
  simpa only [map_zero,add_zero] using! hA.clm_apply (hasDerivAt_const t v)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (g : SmoothCoordinateMetric E)

/-- Differentiating the actual metric-compatibility identity. -/
theorem second_metric_compatibility {x : E} (hx : x ∈ g.domain) (a v w z : E) :
    ⟪fderiv ℝ (fderiv ℝ g.coefficient) x a v w,z⟫ =
      ⟪fderiv ℝ g.coefficient x a (g.christoffel x v w),z⟫ +
      g.inner x (fderiv ℝ (fun y => g.christoffel y v w) x a) z +
      ⟪fderiv ℝ g.coefficient x a w,g.christoffel x v z⟫ +
      g.inner x w (fderiv ℝ (fun y => g.christoffel y v z) x a) := by
  let γ : ℝ → E := fun t => x + t • a
  have hγ : HasDerivAt γ a 0 := by
    simpa only [γ,one_smul,zero_add] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  have hγ0 : γ 0 = x := by simp [γ]
  have hg := (g.smooth x hx).contDiffAt (g.isOpen_domain.mem_nhds hx)
  have hD : HasFDerivAt (fderiv ℝ g.coefficient)
      (fderiv ℝ (fderiv ℝ g.coefficient) x) (γ 0) := by
    simpa only [hγ0] using (hg.fderiv_right (m := 1) (by simp)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hleft : HasDerivAt (fun t => ⟪fderiv ℝ g.coefficient (γ t) v w,z⟫)
      ⟪fderiv ℝ (fderiv ℝ g.coefficient) x a v w,z⟫ 0 := by
    have h0 : HasDerivAt (fun t => fderiv ℝ g.coefficient (γ t))
        (fderiv ℝ (fderiv ℝ g.coefficient) x a) 0 := by
      simpa only [Function.comp_apply] using!
        HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E)
          (E := E →L[ℝ] E →L[ℝ] E) (l := fderiv ℝ g.coefficient)
          (l' := fderiv ℝ (fderiv ℝ g.coefficient) x) (f := γ) (f' := a) 0 hD hγ
    have h1 := hasDerivAt_apply_fixed h0 v
    have h2 := hasDerivAt_apply_fixed h1 w
    simpa only [inner_zero_right,add_zero,zero_add] using! h2.inner ℝ (hasDerivAt_const 0 z)
  have hΓ (b : E) : HasDerivAt (fun t => g.christoffel (γ t) v b)
      (fderiv ℝ (fun y => g.christoffel y v b) x a) 0 := by
    simpa only [hγ0,g.christoffel_zero_left,g.christoffel_zero_right,add_zero] using!
      g.hasDerivAt_christoffel (by simpa only [hγ0] using hx) hγ
        (hasDerivAt_const 0 v) (hasDerivAt_const 0 b)
  have hright := (g.hasDerivAt_inner (by simpa only [hγ0] using hx) hγ
    (hΓ w) (hasDerivAt_const 0 z)).add
    (g.hasDerivAt_inner (by simpa only [hγ0] using hx) hγ
      (hasDerivAt_const 0 w) (hΓ z))
  have heq : (fun t => ⟪fderiv ℝ g.coefficient (γ t) v w,z⟫) =ᶠ[𝓝 0]
      (fun t => g.inner (γ t) (g.christoffel (γ t) v w) z +
        g.inner (γ t) w (g.christoffel (γ t) v z)) := by
    have hd := hγ.continuousAt.tendsto.eventually
      (by simpa only [hγ0] using! g.isOpen_domain.mem_nhds hx)
    filter_upwards [hd] with t ht
    exact (g.christoffel_compatible ht v w z).symm
  have he := hleft.unique (hright.congr_of_eventuallyEq heq)
  simpa only [hγ0,SmoothCoordinateMetric.inner,map_zero,inner_zero_left,inner_zero_right,add_zero,zero_add,add_assoc] using he

end OAI.Geometry.Nikodym.SmoothCoordinateMetric
