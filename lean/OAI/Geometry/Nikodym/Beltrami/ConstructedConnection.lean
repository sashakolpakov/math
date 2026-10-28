import OAI.Geometry.Nikodym.Beltrami.SmoothMetric
import OAI.Geometry.Nikodym.ConnectionUnique
import OAI.Geometry.Nikodym.ParallelMetric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set Filter
open scoped RealInnerProductSpace ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem beltramiCoefficient_compatible {κ : ℝ} {x : E}
    (hx : 0 < beltramiDenominator κ x) (a u v : E) :
    beltramiMetric κ x (beltramiChristoffel κ x a u) v +
      beltramiMetric κ x u (beltramiChristoffel κ x a v) =
      ⟪fderiv ℝ (beltramiCoefficient κ) x a u,v⟫ := by
  let γ : ℝ → E := fun t => x + t • a
  have hγ : HasDerivAt γ a 0 := by
    simpa only [γ,one_smul,zero_add] using!
      (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const a)
  have hγ0 : γ 0 = x := by simp [γ]
  have hexp := hasDerivAt_beltramiMetric (κ := κ) hγ
    (by simpa only [hγ0] using hx.ne') u v
  have hmet := (beltramiSmoothMetric κ).hasDerivAt_inner
    (by simpa only [hγ0,beltramiSmoothMetric_domain,Set.mem_ofPred_eq] using hx) hγ
    (hasDerivAt_const 0 u) (hasDerivAt_const 0 v)
  have he : (fun t => (beltramiSmoothMetric κ).inner (γ t) u v) =
      (fun t => beltramiMetric κ (γ t) u v) := by
    funext t
    exact beltramiSmoothMetric_inner κ (γ t) u v
  rw [he] at hmet
  simpa only [hγ0,beltramiSmoothMetric, OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,
    map_zero,inner_zero_left,inner_zero_right,add_zero] using hexp.unique hmet

/-- The explicit projective Christoffel formula is exactly the connection
constructed by differentiating and inverting the Beltrami metric. -/
theorem beltramiSmoothMetric_christoffel {κ : ℝ} {x : E}
    (hx : 0 < beltramiDenominator κ x) (u v : E) :
    (beltramiSmoothMetric κ).christoffel x u v = beltramiChristoffel κ x u v := by
  apply (beltramiSmoothMetric κ).christoffel_eq_of_symmetric_compatible hx
    (beltramiChristoffel κ x) (beltramiChristoffel_symmetric κ x)
  intro a b c
  simpa only [beltramiSmoothMetric_inner] using! beltramiCoefficient_compatible hx a b c

end OAI.Geometry.Nikodym
