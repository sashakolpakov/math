import OAI.Analysis.PDE.Green.SmallFlux

/-! Weighted small-flux estimates for time test functions. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem regular_product_boundary_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) {r q₀ q₁ v : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hq₀ : ContDiff ℝ 1 q₀) (hq₁ : ContDiff ℝ 1 q₁)
    (hv : Continuous v) (hrne : ∀ x ∈ K, r x = 0 → fderiv ℝ r x ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) (hzero : ∀ x, r x = 0 → q₁ x = 0)
    (hbound : ∀ x, r x = 0 → ‖q₀ x‖ ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      ‖v x * q₀ x + q₁ x‖ ≤ ε * ‖v x‖ + C * ‖r x‖ := by
  obtain ⟨C₀, hC₀, hc₀⟩ := regular_boundary_compact_bound hK hε hr hq₀ hrne hbound
  obtain ⟨C₁, hC₁, hc₁⟩ := regular_zero_compact_bound hK hr hq₁ hrne hzero
  obtain ⟨V, hV⟩ := (hK.image hv).isBounded.exists_norm_le
  refine ⟨C₀ * max V 0 + C₁, by positivity, ?_⟩
  intro x hx
  have hvx : ‖v x‖ ≤ max V 0 := (hV _ (mem_image_of_mem v hx)).trans (le_max_left _ _)
  calc
    ‖v x * q₀ x + q₁ x‖ ≤ ‖v x‖ * ‖q₀ x‖ + ‖q₁ x‖ := by
      simpa only [norm_mul] using norm_add_le (v x * q₀ x) (q₁ x)
    _ ≤ ‖v x‖ * (ε + C₀ * ‖r x‖) + C₁ * ‖r x‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hc₀ x hx) (norm_nonneg _)) (hc₁ x hx)
    _ ≤ _ := by nlinarith [norm_nonneg (r x), mul_le_mul_of_nonneg_left hvx hC₀]

theorem normalCutoffWeight_weighted_flux_bound {m : ℕ} (a b : Fin (m + 1) → ℝ)
    {r q v : (Fin (m + 1) → ℝ) → ℝ} (hr : Continuous r) (hv : Continuous v)
    {ε C W : ℝ} (hε : 0 ≤ ε)
    (hq : ∀ x ∈ Icc a b, ‖q x‖ ≤ ε * ‖v x‖ + C * ‖r x‖)
    (hW : ∀ k : ℕ, (∫ x in Icc a b, normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (k : ℕ) :
    ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖ ≤
      ε * W + ∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * C := by
  have hw : Continuous (fun x => ε * (normalCutoffWeight (r x) k * ‖v x‖)) :=
    continuous_const.mul (((continuous_normalCutoffWeight k).comp hr).mul hv.norm)
  have hs : Continuous (fun x => transitionSlope (-((k : ℝ) + 1) * r x) * C) :=
    (continuous_transitionSlope.comp (continuous_const.mul hr)).mul continuous_const
  have hbound : ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖ ≤
      ∫ x in Icc a b, ε * (normalCutoffWeight (r x) k * ‖v x‖) +
        transitionSlope (-((k : ℝ) + 1) * r x) * C := by
    apply norm_integral_le_of_norm_le (hw.add hs).integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul, Real.norm_of_nonneg (normalCutoffWeight_nonneg (r x) k)]
    calc
      _ ≤ normalCutoffWeight (r x) k * (ε * ‖v x‖ + C * ‖r x‖) :=
        mul_le_mul_of_nonneg_left (hq x hx) (normalCutoffWeight_nonneg (r x) k)
      _ = _ := by
        dsimp only [Pi.add_apply]
        rw [← normalCutoffWeight_mul_norm]
        ring
  rw [integral_add hw.integrableOn_Icc hs.integrableOn_Icc, integral_const_mul] at hbound
  exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_left (hW k) hε) le_rfl)

/-- A weighted Green error bound. The normal flux is split into the test
function times a small flux and a term vanishing on the lateral boundary. -/
theorem weighted_small_normal_divergence_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r q₀ q₁ v : (Fin (m + 1) → ℝ) → ℝ}
    (hr : ContDiff ℝ 2 r) (hq₀ : ContDiff ℝ 1 q₀) (hq₁ : ContDiff ℝ 1 q₁)
    (hv : Continuous v) (hrne : ∀ x ∈ Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in Icc a b, normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hzero : ∀ x, r x = 0 → q₁ x = 0)
    (hbound : ∀ x, r x = 0 → ‖q₀ x‖ ≤ ε)
    (hdecomp : ∀ x, (∑ i, fderiv ℝ r x (Pi.single i 1) * F i x) = v x * q₀ x + q₁ x)
    (hface : CompatibleBoxFaces a b r F) :
    ‖∫ x in (Icc a b) ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ ≤ ε * W := by
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  obtain ⟨C, _, hC⟩ := regular_product_boundary_bound isCompact_Icc
    (hr.of_le (by norm_num)) hq₀ hq₁ hv hrne hε hzero hbound
  have hdc : Continuous divF := continuous_finsetSum _
    (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  have ht := integral_boundaryCutoff_inter_tendsto (μ := volume) (K := Icc a b)
    hr.continuous hdc hdc.integrableOn_Icc
  have hnorm : Tendsto (fun k : ℕ => ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖)
      atTop (𝓝 ‖∫ x in (Icc a b) ∩ {x | r x < 0}, divF x‖) := by
    simpa only [divF, cutoff_divergence_formula a b hab F hF
      (hr.of_le (by norm_num)) hface] using ht.norm
  have hres := integral_transitionSlope_tendsto_zero (μ := volume) (S := Icc a b)
    hr.continuous (continuous_const : Continuous (fun _ : Fin (m + 1) → ℝ => C)).integrableOn_Icc
  have hright : Tendsto (fun k : ℕ => ε * W +
      ∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * C)
      atTop (𝓝 (ε * W)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hres
  apply le_of_tendsto_of_tendsto' hnorm hright
  intro k
  apply normalCutoffWeight_weighted_flux_bound a b hr.continuous hv hε _ hW k
  intro x hx
  dsimp only [q]
  rw [hdecomp]
  exact hC x hx

end OAI.Analysis.PDE.Green
