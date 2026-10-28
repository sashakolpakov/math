import OAI.Analysis.PDE.Green.QuantitativeCutoff
import OAI.Analysis.PDE.Green.SmallFlux

/-! Quantitative cutoff control using geometry only inside the sublevel. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem transition_deriv_zero_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · have hm : IsLocalMin Real.smoothTransition 0 := by
      filter_upwards [] with x
      simpa only [Real.smoothTransition.zero_of_nonpos le_rfl] using Real.smoothTransition.nonneg x
    exact hm.deriv_eq_zero
  · exact transition_deriv_zero_left ht

theorem normalCutoffWeight_zero {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    normalCutoffWeight r k = 0 := by
  unfold normalCutoffWeight
  have ht : -((k : ℝ) + 1) * r ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) hr
  rw [transition_deriv_zero_nonpos ht, mul_zero]

/-- No extension constants outside the domain enter this estimate. In particular,
a locally defined transverse field can be extended arbitrarily away from the
closed sublevel without weakening this bound. -/
theorem normalCutoffWeight_integral_bound_on_sublevel {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r)
    {c C D R : ℝ} (hc : 0 < c) (hC : ∀ t, ‖transitionSlope t‖ ≤ C)
    (hD0 : 0 ≤ D) (hR0 : 0 ≤ R)
    (hmin : ∀ x ∈ Icc a b, r x < 0 →
      c ≤ (∑ i, fderiv ℝ r x (Pi.single i 1) * F i x) + r x ^ 2)
    (hD : ∀ x ∈ Icc a b, r x < 0 →
      ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ ≤ D)
    (hR : ∀ x ∈ Icc a b, r x < 0 → ‖r x‖ ≤ R)
    (hface : CompatibleBoxFaces a b r F) (k : ℕ) :
    (∫ x in Icc a b, normalCutoffWeight (r x) k) ≤
      ((D + C * R) * boxVolume a b) / c := by
  let g := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  have hC0 : 0 ≤ C := (norm_nonneg (transitionSlope 0)).trans (hC 0)
  have hg : Continuous g := continuous_finsetSum _ (fun i _ =>
    (continuous_directional hr (Pi.single i 1)).mul (hF i).continuous)
  have hd : Continuous divF := continuous_finsetSum _
    (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  have hw : Continuous (fun x => normalCutoffWeight (r x) k) :=
    (continuous_normalCutoffWeight k).comp hr.continuous
  have hwg : Continuous (fun x => normalCutoffWeight (r x) k * g x) := hw.mul hg
  have hright : Continuous (fun x => normalCutoffWeight (r x) k * g x + C * R) :=
    hwg.add continuous_const
  have hmain : (∫ x in Icc a b, c * normalCutoffWeight (r x) k) ≤
      ∫ x in Icc a b, normalCutoffWeight (r x) k * g x + C * R := by
    apply setIntegral_mono_on (continuous_const.mul hw).integrableOn_Icc hright.integrableOn_Icc
      measurableSet_Icc
    intro x hx
    change c * normalCutoffWeight (r x) k ≤ normalCutoffWeight (r x) k * g x + C * R
    by_cases hneg : r x < 0
    · have hh := mul_le_mul_of_nonneg_left (hmin x hx hneg) (normalCutoffWeight_nonneg (r x) k)
      have hs := (normalCutoffWeight_square_bound hC (r x) k).trans
        (mul_le_mul_of_nonneg_left (hR x hx hneg) hC0)
      change normalCutoffWeight (r x) k * c ≤ normalCutoffWeight (r x) k * (g x + r x ^ 2) at hh
      nlinarith
    · rw [normalCutoffWeight_zero (le_of_not_gt hneg), mul_zero, zero_mul, zero_add]
      exact mul_nonneg hC0 hR0
  have hchi : Continuous (fun x => boundaryCutoff (r x) k) := (contDiff_boundaryCutoff hr k).continuous
  have hchiD : Continuous (fun x => boundaryCutoff (r x) k * divF x) := hchi.mul hd
  have hdiv : (∫ x in Icc a b, boundaryCutoff (r x) k * divF x) ≤ D * boxVolume a b := by
    change (∫ x in Icc a b, boundaryCutoff (r x) k * divF x) ≤
      D * (∫ x in Icc a b, (1 : ℝ))
    rw [← integral_const_mul]
    apply setIntegral_mono_on hchiD.integrableOn_Icc continuous_const.integrableOn_Icc measurableSet_Icc
    intro x hx
    change boundaryCutoff (r x) k * divF x ≤ D * 1
    rw [mul_one]
    by_cases hneg : r x < 0
    · have hchi0 : 0 ≤ boundaryCutoff (r x) k := Real.smoothTransition.nonneg _
      have hchi1 : boundaryCutoff (r x) k ≤ 1 := Real.smoothTransition.le_one _
      have hnorm : ‖boundaryCutoff (r x) k * divF x‖ ≤ D := by
        rw [norm_mul, Real.norm_of_nonneg hchi0]
        calc
          _ ≤ boundaryCutoff (r x) k * D := mul_le_mul_of_nonneg_left (hD x hx hneg) hchi0
          _ ≤ 1 * D := mul_le_mul_of_nonneg_right hchi1 hD0
          _ = D := one_mul D
      exact (le_abs_self _).trans hnorm
    · rw [boundaryCutoff_zero (le_of_not_gt hneg), zero_mul]
      exact hD0
  have hconst : (∫ x in Icc a b, C * R) = C * R * boxVolume a b := by
    change _ = C * R * (∫ x in Icc a b, (1 : ℝ))
    rw [← integral_const_mul]
    simp only [mul_one]
  rw [integral_const_mul, integral_add hwg.integrableOn_Icc continuous_const.integrableOn_Icc,
    hconst] at hmain
  have hformula := cutoff_divergence_formula a b hab F hF hr hface k
  change (∫ x in Icc a b, boundaryCutoff (r x) k * divF x) =
    ∫ x in Icc a b, normalCutoffWeight (r x) k * g x at hformula
  rw [← hformula] at hmain
  apply (le_div_iff₀ hc).mpr
  nlinarith

end OAI.Analysis.PDE.Green
