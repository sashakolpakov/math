import OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Oscillatory Tail Tools -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools.Construction

noncomputable section

section

/-! A monotone-weight integration-by-parts bound for oscillatory Gaussian tails. -/

open _root_.MeasureTheory Set

theorem monotone_weight_oscillatory_bound
    {a b : ℝ} (hab : a ≤ b) (u u' : ℝ → ℝ) (v v' : ℝ → ℂ)
    (hu : ∀ x ∈ uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ uIcc a b, HasDerivAt v (v' x) x)
    (hui : IntervalIntegrable u' volume a b) (hvi : IntervalIntegrable v' volume a b)
    (hu0 : ∀ x ∈ uIcc a b, 0 ≤ u x)
    (hu' : ∀ x ∈ uIcc a b, u' x ≤ 0)
    (hv1 : ∀ x ∈ uIcc a b, ‖v x‖ ≤ 1) :
    ‖∫ x in a..b, (u x : ℂ) * v' x‖ ≤ 2 * u a := by
  have huiC : IntervalIntegrable (fun x => (u' x : ℂ)) volume a b := ⟨hui.1.ofReal, hui.2.ofReal⟩
  have huC : ∀ x ∈ uIcc a b, HasDerivAt (fun t => (u t : ℂ)) (u' x : ℂ) x :=
    fun x hx => (hu x hx).ofReal_comp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (HasDerivAt.continuousOn huC) (HasDerivAt.continuousOn hv)
    (fun x hx => huC x (mem_Icc_of_Ioo hx)) (fun x hx => hv x (mem_Icc_of_Ioo hx)) huiC hvi
  have hJ : ‖∫ x in a..b, (u' x : ℂ) * v x‖ ≤ u a - u b := by
    calc
      _ ≤ ∫ x in a..b, -u' x := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hui.neg
        exact Filter.Eventually.of_forall fun x hx => by
          have hxcc : x ∈ uIcc a b := by rw [uIcc_of_le hab]; exact ⟨hx.1.le, hx.2⟩
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hu' x hxcc)]
          exact mul_le_of_le_one_right (neg_nonneg.mpr (hu' x hxcc)) (hv1 x hxcc)
      _ = u a - u b := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt hu hui]
        ring
  have hbound (x : ℝ) (hx : x ∈ uIcc a b) : ‖(u x : ℂ) * v x‖ ≤ u x := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hu0 x hx)]
    exact mul_le_of_le_one_right (hu0 x hx) (hv1 x hx)
  rw [hparts]
  calc
    _ ≤ ‖(u b : ℂ) * v b - (u a : ℂ) * v a‖ + ‖∫ x in a..b, (u' x : ℂ) * v x‖ := norm_sub_le _ _
    _ ≤ (‖(u b : ℂ) * v b‖ + ‖(u a : ℂ) * v a‖) + (u a - u b) :=
      add_le_add (norm_sub_le _ _) hJ
    _ ≤ (u b + u a) + (u a - u b) :=
      add_le_add (add_le_add (hbound b right_mem_uIcc) (hbound a left_mem_uIcc)) le_rfl
    _ = 2 * u a := by ring

end

/-! Two integrations by parts for the planar Gaussian tail argument. -/

open _root_.MeasureTheory

theorem integral_second_derivative_transfer
    (u u' u'' v v' v'' : ℝ → ℂ)
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hv : ∀ x, HasDerivAt v (v' x) x) (hv' : ∀ x, HasDerivAt v' (v'' x) x)
    (huv'' : Integrable (u * v'')) (hu'v' : Integrable (u' * v'))
    (hu''v : Integrable (u'' * v)) (huv' : Integrable (u * v'))
    (hu'v : Integrable (u' * v)) :
    (∫ x, u x * v'' x) = ∫ x, u'' x * v x := by
  have h1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hu x) (fun x _ => hv' x) huv'' hu'v' huv'
  have h2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hu' x) (fun x _ => hv x) hu'v' hu''v hu'v
  rw [h1, h2, neg_neg]

theorem integral_planar_second_derivative_transfer
    (u u' u'' v v' v'' : ℝ × ℝ → ℂ)
    (hu : ∀ x y, HasDerivAt (fun t => u (t, y)) (u' (x, y)) x)
    (hu' : ∀ x y, HasDerivAt (fun t => u' (t, y)) (u'' (x, y)) x)
    (hv : ∀ x y, HasDerivAt (fun t => v (t, y)) (v' (x, y)) x)
    (hv' : ∀ x y, HasDerivAt (fun t => v' (t, y)) (v'' (x, y)) x)
    (huv'' : Integrable (u * v'')) (hu'v' : Integrable (u' * v'))
    (hu''v : Integrable (u'' * v)) (huv' : Integrable (u * v'))
    (hu'v : Integrable (u' * v)) :
    (∫ z, u z * v'' z) = ∫ z, u'' z * v z := by
  change (∫ z, u z * v'' z ∂volume.prod volume) = ∫ z, u'' z * v z ∂volume.prod volume
  rw [integral_prod_symm (fun z => u z * v'' z) huv'',
    integral_prod_symm (fun z => u'' z * v z) hu''v]
  apply integral_congr_ae
  filter_upwards [huv''.prod_left_ae, hu'v'.prod_left_ae, hu''v.prod_left_ae,
    huv'.prod_left_ae, hu'v.prod_left_ae] with y h1 h2 h3 h4 h5
  exact integral_second_derivative_transfer
    (fun x => u (x, y)) (fun x => u' (x, y)) (fun x => u'' (x, y))
    (fun x => v (x, y)) (fun x => v' (x, y)) (fun x => v'' (x, y))
    (fun x => hu x y) (fun x => hu' x y) (fun x => hv x y) (fun x => hv' x y)
    h1 h2 h3 h4 h5

theorem integral_planar_second_derivative_transfer_right
    (u u' u'' v v' v'' : ℝ × ℝ → ℂ)
    (hu : ∀ x y, HasDerivAt (fun t => u (x, t)) (u' (x, y)) y)
    (hu' : ∀ x y, HasDerivAt (fun t => u' (x, t)) (u'' (x, y)) y)
    (hv : ∀ x y, HasDerivAt (fun t => v (x, t)) (v' (x, y)) y)
    (hv' : ∀ x y, HasDerivAt (fun t => v' (x, t)) (v'' (x, y)) y)
    (huv'' : Integrable (u * v'')) (hu'v' : Integrable (u' * v'))
    (hu''v : Integrable (u'' * v)) (huv' : Integrable (u * v'))
    (hu'v : Integrable (u' * v)) :
    (∫ z, u z * v'' z) = ∫ z, u'' z * v z := by
  change (∫ z, u z * v'' z ∂volume.prod volume) = ∫ z, u'' z * v z ∂volume.prod volume
  rw [integral_prod (fun z => u z * v'' z) huv'',
    integral_prod (fun z => u'' z * v z) hu''v]
  apply integral_congr_ae
  filter_upwards [huv''.prod_right_ae, hu'v'.prod_right_ae, hu''v.prod_right_ae,
    huv'.prod_right_ae, hu'v.prod_right_ae] with x h1 h2 h3 h4 h5
  exact integral_second_derivative_transfer
    (fun y => u (x, y)) (fun y => u' (x, y)) (fun y => u'' (x, y))
    (fun y => v (x, y)) (fun y => v' (x, y)) (fun y => v'' (x, y))
    (fun y => hu x y) (fun y => hu' x y) (fun y => hv x y) (fun y => hv' x y)
    h1 h2 h3 h4 h5

end

end OAI.RepresentationTheory.Weil.Local.OscillatoryTailTools.Construction
