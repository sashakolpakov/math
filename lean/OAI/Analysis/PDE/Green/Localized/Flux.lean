import OAI.Analysis.PDE.Green.WeightedFlux
import OAI.Analysis.PDE.Green.Localized.Divergence

/-! Quantitative small-flux estimates localized to an active time test. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem regular_boundary_eventual_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {r q : E → ℝ} {x : E} {B : ℝ}
    (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hrne : fderiv ℝ r x ≠ 0) (hrx : r x = 0)
    (hz : ∀ᶠ y in 𝓝 x, r y = 0 → ‖q y‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ B + C * ‖r y‖ := by
  let r' := fderiv ℝ r x
  let hsurj := OAI.Analysis.PDE.Dirichlet.real_linear_form_range_top r' hrne
  let φ := (hr.hasStrictFDerivAt (by norm_num) (x := x)).implicitFunctionDataOfComplemented
    r r' hsurj r'.ker_closedComplemented_of_finiteDimensional_range
  have hzero : ∀ᶠ y in 𝓝 φ.pt, φ.leftFun y = φ.leftFun φ.pt → ‖q y‖ ≤ B := by
    change ∀ᶠ y in 𝓝 x, r y = r x → ‖q y‖ ≤ B
    exact hz.mono (fun y hy hyr => hy (hyr.trans hrx))
  simpa only [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented, hrx, sub_zero]
    using implicit_boundary_local_bound φ (hq.hasStrictFDerivAt (by norm_num)) hzero

theorem compact_offset_local_bound
    {E : Type*} [TopologicalSpace E] {K : Set E} (hK : IsCompact K) {q r g : E → ℝ}
    (hlocal : ∀ x ∈ K, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ y in 𝓝 x, ‖q y‖ ≤ g y + C * ‖r y‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ g y + C * ‖r y‖ := by
  classical
  choose C hC hloc using hlocal
  let U (x : E) (hx : x ∈ K) : Set E := {y | ‖q y‖ ≤ g y + C x hx * ‖r y‖}
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hloc
  refine ⟨∑ x ∈ t, C x x.property, Finset.sum_nonneg (fun x _ => hC x x.property), ?_⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.mp (ht hy)
  have hle : C x x.property ≤ ∑ z ∈ t, C z z.property :=
    Finset.single_le_sum (f := fun z : K => C z z.property) (fun z _ => hC z z.property) hx
  exact hxy.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hle (norm_nonneg _)))

theorem localized_product_boundary_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) {r q₀ q₁ v : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hq₀ : ContDiff ℝ 1 q₀) (hq₁ : ContDiff ℝ 1 q₁)
    (hv : Continuous v) {ε : ℝ} (hε : 0 ≤ ε)
    (hloc : ∀ x ∈ K, r x = 0 →
      (fderiv ℝ r x ≠ 0 ∧ (∀ᶠ y in 𝓝 x, r y = 0 → ‖q₀ y‖ ≤ ε) ∧
        (∀ᶠ y in 𝓝 x, r y = 0 → q₁ y = 0)) ∨
      (v =ᶠ[𝓝 x] (fun _ => 0)) ∧ (q₁ =ᶠ[𝓝 x] (fun _ => 0))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K,
      ‖v x * q₀ x + q₁ x‖ ≤ ε * ‖v x‖ + C * ‖r x‖ := by
  apply compact_offset_local_bound hK
  intro x hx
  by_cases hrx : r x = 0
  · rcases hloc x hx hrx with ⟨hreg, hzero, hone⟩ | ⟨hzero, hone⟩
    · obtain ⟨C₀, hC₀, hc₀⟩ := regular_boundary_eventual_bound hr hq₀ hreg hrx hzero
      have hone' : ∀ᶠ y in 𝓝 x, r y = 0 → ‖q₁ y‖ ≤ 0 := by
        filter_upwards [hone] with y hy hyr
        simp only [hy hyr, norm_zero, le_refl]
      obtain ⟨C₁, hC₁, hc₁⟩ := regular_boundary_eventual_bound hr hq₁ hreg hrx hone'
      have hV : ∀ᶠ y in 𝓝 x, ‖v y‖ < ‖v x‖ + 1 :=
        hv.norm.continuousAt.eventually (gt_mem_nhds (by linarith))
      refine ⟨C₀ * (‖v x‖ + 1) + C₁, by positivity, ?_⟩
      filter_upwards [hc₀, hc₁, hV] with y hy₀ hy₁ hyV
      calc
        ‖v y * q₀ y + q₁ y‖ ≤ ‖v y‖ * ‖q₀ y‖ + ‖q₁ y‖ := by
          simpa only [norm_mul] using norm_add_le (v y * q₀ y) (q₁ y)
        _ ≤ ‖v y‖ * (ε + C₀ * ‖r y‖) + (0 + C₁ * ‖r y‖) :=
          add_le_add (mul_le_mul_of_nonneg_left hy₀ (norm_nonneg _)) hy₁
        _ ≤ _ := by
          nlinarith [mul_le_mul_of_nonneg_right hyV.le (mul_nonneg hC₀ (norm_nonneg (r y)))]
    · refine ⟨0, le_rfl, ?_⟩
      filter_upwards [hzero, hone] with y hyv hyq
      simp only [hyv, hyq, zero_mul, add_zero, norm_zero, mul_zero, le_refl]
  · obtain ⟨C, hC, hc⟩ := nonzero_local_bound hr.continuous
      ((hv.mul hq₀.continuous).add hq₁.continuous) hrx
    refine ⟨C, hC, hc.mono (fun y hy => ?_)⟩
    exact hy.trans (le_add_of_nonneg_left (mul_nonneg hε (norm_nonneg _)))

theorem weighted_small_divergence_of_normal_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r v : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r) (hv : Continuous v)
    {ε W C : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in Icc a b, normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hbound : ∀ x ∈ Icc a b, ‖∑ i, fderiv ℝ r x (Pi.single i 1) * F i x‖ ≤
      ε * ‖v x‖ + C * ‖r x‖)
    (hface : CompatibleBoxFaces a b r F) :
    ‖∫ x in (Icc a b) ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ ≤ ε * W := by
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  have hdc : Continuous divF := continuous_finsetSum _
    (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  have ht := integral_boundaryCutoff_inter_tendsto (μ := volume) (K := Icc a b)
    hr.continuous hdc hdc.integrableOn_Icc
  have hnorm : Tendsto (fun k : ℕ => ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖)
      atTop (𝓝 ‖∫ x in (Icc a b) ∩ {x | r x < 0}, divF x‖) := by
    simpa only [divF, cutoff_divergence_formula a b hab F hF hr hface] using ht.norm
  have hres := integral_transitionSlope_tendsto_zero (μ := volume) (S := Icc a b)
    hr.continuous (continuous_const : Continuous (fun _ : Fin (m + 1) → ℝ => C)).integrableOn_Icc
  have hright : Tendsto (fun k : ℕ => ε * W +
      ∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * C)
      atTop (𝓝 (ε * W)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hres
  exact le_of_tendsto_of_tendsto' hnorm hright
    (fun k => normalCutoffWeight_weighted_flux_bound a b hr.continuous hv hε hbound hW k)

end OAI.Analysis.PDE.Green
