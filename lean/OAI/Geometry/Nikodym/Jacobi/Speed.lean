import OAI.Geometry.Nikodym.Jacobi.Scaling

noncomputable section
namespace OAI.Geometry.Nikodym.IsSpaceFormJacobiField

open Set
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {g : SmoothCoordinateMetric E} {κ : ℝ} {γ v : ℝ → E} {I : Set ℝ}

/-- The exact Jacobi metric for arbitrary nonzero affine speed, obtained
by an actual time change to unit speed. -/
theorem normal_metric_speed {J₁ A₁ J₂ A₂ : ℝ → E}
    (h1 : IsSpaceFormJacobiField g κ γ v J₁ A₁ I)
    (h2 : IsSpaceFormJacobiField g κ γ v J₂ A₂ I)
    (hγ : IsMetricGeodesic g γ v I) (hI : Convex ℝ I) (h0 : 0 ∈ I)
    {c : ℝ} (hc : 0 < c) (hspeed : ∀ t ∈ I, g.inner (γ t) (v t) (v t) = c^2)
    (h10 : J₁ 0 = 0) (h20 : J₂ 0 = 0) {t : ℝ} (ht : t ∈ I) :
    g.inner (γ t) (J₁ t) (J₂ t) =
      t^2 * (g.inner (γ 0) (A₁ 0) (v 0) * g.inner (γ 0) (A₂ 0) (v 0) / c^2) +
      (curvatureSin κ (c*t) / c)^2 * (g.inner (γ 0) (A₁ 0) (A₂ 0) -
        g.inner (γ 0) (A₁ 0) (v 0) * g.inner (γ 0) (A₂ 0) (v 0) / c^2) := by
  have hc0 := hc.ne'
  let I' : Set ℝ := {s | c⁻¹*s ∈ I}
  have hI' : Convex ℝ I' := hI.smul_preimage c⁻¹
  have h0' : (0 : ℝ) ∈ I' := by
    change c⁻¹ * 0 ∈ I
    simpa only [mul_zero] using h0
  have ht' : c*t ∈ I' := by
    change c⁻¹ * (c*t) ∈ I
    simpa only [inv_mul_cancel_left₀ hc0] using ht
  have hg' : IsMetricGeodesic g (fun s => γ (c⁻¹*s))
      (fun s => c⁻¹ • v (c⁻¹*s)) I' := by
    simpa only [add_zero] using hγ.affine_reparam c⁻¹ 0
  have hu : ∀ s ∈ I', g.inner (γ (c⁻¹*s))
      (c⁻¹ • v (c⁻¹*s)) (c⁻¹ • v (c⁻¹*s)) = 1 := by
    intro s hs
    simp only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_smul,real_inner_smul_left,inner_smul_right]
    change c⁻¹ * (c⁻¹ * g.inner (γ (c⁻¹*s)) (v (c⁻¹*s)) (v (c⁻¹*s))) = 1
    rw [hspeed _ hs]
    field_simp
  have h1' := (h1.scale_time c⁻¹).unit hu
  have h2' := (h2.scale_time c⁻¹).unit hu
  have he := h1'.normal_metric h2' hg' hI' h0' hu
    (by simpa only [mul_zero] using h10) (by simpa only [mul_zero] using h20) ht'
  simp only [inv_mul_cancel_left₀ hc0,mul_zero] at he
  simp only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner,map_smul,real_inner_smul_left,inner_smul_right] at he
  change g.inner (γ t) (J₁ t) (J₂ t) = _ at he
  rw [he]
  simp only [OAI.Geometry.Nikodym.SmoothCoordinateMetric.inner]
  field_simp

end OAI.Geometry.Nikodym.IsSpaceFormJacobiField
