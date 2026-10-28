import OAI.Geometry.Nikodym.Beltrami.Metric

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_beltramiDenominator (κ : ℝ) :
    ContDiff ℝ ∞ (beltramiDenominator κ : E → ℝ) :=
  contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem hasDerivAt_beltramiDenominator {κ t : ℝ} {γ : ℝ → E} {w : E}
    (hγ : HasDerivAt γ w t) :
    HasDerivAt (fun s => beltramiDenominator κ (γ s)) (2*κ*⟪γ t,w⟫) t := by
  convert (hγ.norm_sq.const_mul κ).const_add 1 using 1
  · rfl
  · ring

/-- The connection is metric compatible. Together with symmetry in the two
vector arguments, this verifies the Christoffel formula instead of assuming
the straight-line equation for the metric. -/
theorem hasDerivAt_beltramiMetric {κ t : ℝ} {γ : ℝ → E} {w : E}
    (hγ : HasDerivAt γ w t) (hq : beltramiDenominator κ (γ t) ≠ 0) (u v : E) :
    HasDerivAt (fun s => beltramiMetric κ (γ s) u v)
      (beltramiMetric κ (γ t) (beltramiChristoffel κ (γ t) w u) v +
        beltramiMetric κ (γ t) u (beltramiChristoffel κ (γ t) w v)) t := by
  have hdq := hasDerivAt_beltramiDenominator (κ := κ) hγ
  have hdu : HasDerivAt (fun s => ⟪γ s,u⟫) ⟪w,u⟫ t := by
    simpa using hγ.inner ℝ (hasDerivAt_const t u)
  have hdv : HasDerivAt (fun s => ⟪γ s,v⟫) ⟪w,v⟫ t := by
    simpa using hγ.inner ℝ (hasDerivAt_const t v)
  have hd := ((hdq.mul_const ⟪u,v⟫).sub ((hdu.const_mul κ).mul hdv)).div
    (hdq.pow 2) (pow_ne_zero 2 hq)
  convert hd using 1
  · rfl
  · simp only [beltramiMetric,beltramiChristoffel,inner_smul_left,inner_smul_right,
      inner_add_left,inner_add_right,conj_trivial]
    dsimp [beltramiDenominator] at hq ⊢
    rw [real_inner_comm u w]
    field_simp
    ring

/-- A metric geodesic has a conserved rescaled velocity in Beltrami
coordinates. This is the differential identity responsible for geodesic
straightening in both signs of curvature. -/
theorem hasDerivAt_rescaled_geodesic_velocity {κ t : ℝ} {γ v : ℝ → E}
    (hγ : HasDerivAt γ (v t) t)
    (hv : HasDerivAt v (-beltramiChristoffel κ (γ t) (v t) (v t)) t)
    (hq : beltramiDenominator κ (γ t) ≠ 0) :
    HasDerivAt (fun s => (beltramiDenominator κ (γ s))⁻¹ • v s) 0 t := by
  have hd := ((hasDerivAt_beltramiDenominator (κ := κ) hγ).inv hq).smul hv
  convert hd using 1
  simp only [beltramiChristoffel,Pi.inv_apply,smul_smul,
    ← neg_smul,← add_smul]
  convert zero_smul ℝ (v t) |>.symm using 2
  field_simp
  ring

end OAI.Geometry.Nikodym
