import OAI.Geometry.Nikodym.Riemannian.Coercivity

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology

namespace OAI.Geometry.Nikodym

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem quadratic_difference_le (A B : E →L[ℝ] E) (v : E) :
    |⟪A v,v⟫-⟪B v,v⟫| ≤ ‖A-B‖*‖v‖^2 := by
  rw [← inner_sub_left]
  calc
    |⟪A v-B v,v⟫| ≤ ‖A v-B v‖*‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A-B‖*‖v‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right ((A-B).le_opNorm v) (norm_nonneg v)
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
theorem quadratic_upper_le (A : E →L[ℝ] E) (v : E) :
    ⟪A v,v⟫ ≤ ‖A‖*‖v‖^2 := by
  have h := quadratic_difference_le A 0 v
  simp only [zero_apply,inner_zero_left,sub_zero] at h
  exact (le_abs_self ⟪A v,v⟫).trans h

namespace SmoothCoordinateMetric

/-- A smooth positive coordinate metric is uniformly comparable with the
fixed Euclidean norm on a sufficiently small closed coordinate ball. -/
theorem locally_uniform_elliptic (g : SmoothCoordinateMetric E)
    {x₀ : E} (hx₀ : x₀ ∈ g.domain) :
    ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧
      closedBall x₀ r ⊆ g.domain ∧
      ∀ x ∈ closedBall x₀ r, ∀ v : E,
        c*‖v‖^2 ≤ g.inner x v v ∧ g.inner x v v ≤ C*‖v‖^2 := by
  obtain ⟨a,ha,hcoer⟩ := g.coercive hx₀
  have hcont : ContinuousAt g.coefficient x₀ :=
    (g.smooth.continuousOn x₀ hx₀).continuousAt (g.isOpen_domain.mem_nhds hx₀)
  have hnear : ∀ᶠ x in 𝓝 x₀, x ∈ g.domain ∧
      ‖g.coefficient x-g.coefficient x₀‖ < a/2 := by
    filter_upwards [g.isOpen_domain.mem_nhds hx₀,
      hcont.preimage_mem_nhds (ball_mem_nhds (g.coefficient x₀) (half_pos ha))] with x hx hg
    exact ⟨hx,by simpa only [mem_preimage,mem_ball,dist_eq_norm] using hg⟩
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hhalf : ρ/2 < ρ := by linarith
  refine ⟨ρ/2,a/2,‖g.coefficient x₀‖+a/2+1,half_pos hρ,half_pos ha,by positivity,?_,?_⟩
  · intro x hx
    exact (hball (mem_ball.mpr ((mem_closedBall.mp hx).trans_lt hhalf))).1
  · intro x hx v
    have hxin : x ∈ ball x₀ ρ := mem_ball.mpr ((mem_closedBall.mp hx).trans_lt hhalf)
    have hd := (hball hxin).2.le
    have hdiff : |g.inner x v v-g.inner x₀ v v| ≤ (a/2)*‖v‖^2 :=
      (quadratic_difference_le (g.coefficient x) (g.coefficient x₀) v).trans
        (mul_le_mul_of_nonneg_right hd (sq_nonneg ‖v‖))
    have hbase := hcoer v
    have hupper : g.inner x₀ v v ≤ ‖g.coefficient x₀‖*‖v‖^2 :=
      quadratic_upper_le (g.coefficient x₀) v
    constructor
    · have h := (abs_le.mp hdiff).1
      nlinarith
    · have h := (abs_le.mp hdiff).2
      nlinarith [sq_nonneg ‖v‖]

end SmoothCoordinateMetric
end OAI.Geometry.Nikodym
