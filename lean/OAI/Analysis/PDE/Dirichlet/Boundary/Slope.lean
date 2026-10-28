import OAI.Analysis.PDE.Dirichlet.Boundary.Normal
import OAI.Analysis.PDE.Dirichlet.AffineField

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

section Normed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Differentiate an absolute comparison on the inward side of a regular boundary. -/
theorem inward_absolute_derivative_bound {u w r : E → ℝ} {x v : E}
    (hu : DifferentiableAt ℝ u x) (hw : DifferentiableAt ℝ w x)
    (hr : DifferentiableAt ℝ r x) (hux : u x = 0) (hwx : w x = 0) (hrx : r x = 0)
    (hcontrol : ∀ᶠ y in 𝓝 x, r y < 0 → |u y| ≤ w y)
    (hinward : fderiv ℝ r x v < 0) : |fderiv ℝ u x v| ≤ fderiv ℝ w x v := by
  have hline : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
  have hslope (f : E → ℝ) (hf : DifferentiableAt ℝ f x) (hfx : f x = 0) :
      Tendsto (fun t : ℝ ↦ f (x + t • v) / t) (𝓝[>] 0) (𝓝 (fderiv ℝ f x v)) := by
    have hf' : DifferentiableAt ℝ f (x + (0 : ℝ) • v) := by simpa using hf
    simpa [hfx, div_eq_inv_mul] using
      (hf'.hasFDerivAt.comp_hasDerivAt 0 hline).tendsto_slope_zero_right
  have hpoint : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hneg : ∀ᶠ t : ℝ in 𝓝[>] 0, r (x + t • v) / t < 0 :=
    (hslope r hr hrx).eventually (eventually_lt_nhds hinward)
  have hle : ∀ᶠ t : ℝ in 𝓝[>] 0, |u (x + t • v) / t| ≤ w (x + t • v) / t := by
    filter_upwards [hpoint.eventually hcontrol, hneg, self_mem_nhdsWithin] with t hc hn ht
    have htpos : 0 < t := ht
    have hrneg : r (x + t • v) < 0 := by simpa using (div_lt_iff₀ htpos).mp hn
    simpa only [abs_div, abs_of_pos htpos] using
      div_le_div_of_nonneg_right (hc hrneg) htpos.le
  exact le_of_tendsto_of_tendsto (hslope u hu hux).abs (hslope w hw hwx) hle

end Normed

section InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem boundary_derivative_of_quadratic_barrier {u r : E → ℝ} {v : E} {M c : ℝ}
    (hu : DifferentiableAt ℝ u 0) (hr : DifferentiableAt ℝ r 0)
    (hu0 : u 0 = 0) (hr0 : r 0 = 0)
    (hcontrol : ∀ᶠ y in 𝓝 (0 : E), r y < 0 → |u y| ≤ M * ‖y‖ ^ 2 - c * r y)
    (hinward : fderiv ℝ r 0 v < 0) : |fderiv ℝ u 0 v| ≤ -c * fderiv ℝ r 0 v := by
  let w : E → ℝ := fun y ↦ M • ‖y‖ ^ 2 + (-c) • r y
  have hq : DifferentiableAt ℝ (fun y : E ↦ ‖y‖ ^ 2) 0 :=
    ((contDiff_norm_sq ℝ : ContDiff ℝ 1 (fun y : E ↦ ‖y‖ ^ 2)).differentiable (by norm_num)) 0
  have hw := (hq.hasFDerivAt.const_smul M).add (hr.hasFDerivAt.const_smul (-c))
  have hw0 : w 0 = 0 := by simp [w, hr0]
  have hwD : fderiv ℝ w 0 v = -c * fderiv ℝ r 0 v := by
    have heq : fderiv ℝ w 0 = M • fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) 0 +
        (-c) • fderiv ℝ r 0 := hw.fderiv
    rw [heq, fderiv_norm_sq_apply]
    simp
  have hbound : |fderiv ℝ u 0 v| ≤ fderiv ℝ w 0 v := by
    apply inward_absolute_derivative_bound (w := w) hu hw.differentiableAt hr hu0 hw0 hr0 ?_ hinward
    simpa only [w, smul_eq_mul, neg_mul, ← sub_eq_add_neg] using hcontrol
  simpa only [hwD] using hbound

/-- The affine-field barrier controls a genuine normal-tangential Hessian
entry when the infinitesimal rotation sends the normal into the tangent space. -/
theorem boundary_mixed_hessian_of_affine_barrier {u r : E → ℝ} {e v : E}
    {A : E →L[ℝ] E} {a M c : ℝ}
    (hu : ContDiff ℝ 2 u) (hr : DifferentiableAt ℝ r 0) (hr0 : r 0 = 0)
    (hfactor : fderiv ℝ u 0 = a • fderiv ℝ r 0)
    (he : fderiv ℝ r 0 e = 0) (hAv : fderiv ℝ r 0 (A v) = 0)
    (hinward : fderiv ℝ r 0 v < 0)
    (hcontrol : ∀ᶠ y in 𝓝 (0 : E), r y < 0 →
      |affineDerivative u e A y| ≤ M * ‖y‖ ^ 2 - c * r y) :
    |fderiv ℝ (fderiv ℝ u) 0 v e| ≤ -c * fderiv ℝ r 0 v := by
  have hX : ContDiff ℝ 1 (affineDerivative u e A) :=
    contDiff_affineDerivative hu (by norm_num) e A
  have hX0 : affineDerivative u e A 0 = 0 := by
    simp [affineDerivative, hfactor, he]
  have hDX : fderiv ℝ (affineDerivative u e A) 0 v = fderiv ℝ (fderiv ℝ u) 0 v e := by
    have h := directionalDerivative_affineDerivative hu e A v (0 : E)
    simpa only [directionalDerivative, map_zero, add_zero, hfactor, smul_apply,
      smul_eq_mul, hAv, mul_zero, zero_add] using h
  have hb := boundary_derivative_of_quadratic_barrier
    ((hX.differentiable (by norm_num)) 0) hr hX0 hr0 hcontrol hinward
  simpa only [hDX] using hb

end InnerProduct
end OAI.Analysis.PDE.Dirichlet
