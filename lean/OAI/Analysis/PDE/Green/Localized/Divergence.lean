import OAI.Analysis.PDE.Green.EuclideanCell
import OAI.Analysis.PDE.Green.SmallFlux

/-! Localized Green infrastructure. Regularity of the defining function is
needed only where the flux is active; it may be degenerate away from the
support of a time test. The proof uses the same actual cutoff limit. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem regular_or_locally_zero_compact_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set E} (hK : IsCompact K) {r q : E → ℝ}
    (hr : ContDiff ℝ 1 r) (hq : ContDiff ℝ 1 q)
    (hreg : ∀ x ∈ K, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ q =ᶠ[𝓝 x] (fun _ => 0))
    (hz : ∀ x, r x = 0 → q x = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ‖q y‖ ≤ C * ‖r y‖ := by
  apply compact_local_bound hK
  intro x hx
  by_cases hrx : r x = 0
  · rcases hreg x hx hrx with h | h
    · exact regular_zero_local_bound hr hq h hrx hz
    · refine ⟨0, le_rfl, ?_⟩
      filter_upwards [h] with y hy
      simp only [hy, norm_zero, zero_mul, le_refl]
  · exact nonzero_local_bound hr.continuous hq.continuous hrx

theorem integral_divergence_cell_of_normal_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Icc a b,
      ‖∑ i, fderiv ℝ r x (Pi.single i 1) * F i x‖ ≤ C * ‖r x‖)
    (hzero : ∀ x, r x = 0 → ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x = 0)
    (hface : CompatibleBoxFaces a b r F) :
    (∫ x in Icc a b ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 0 := by
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let β := fun x => q x / r x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  have hβ : IntegrableOn β (Icc a b) := by
    change Integrable (q / r) (volume.restrict (Icc a b))
    apply (show IntegrableOn (fun _ : Fin (m + 1) → ℝ => C) (Icc a b) volume from
      continuous_const.integrableOn_Icc).mono'
      (hq.continuous.measurable.div hr.continuous.measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    change ‖q x / r x‖ ≤ C
    by_cases hrx : r x = 0
    · simpa [hrx] using hC0
    · rw [norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr hrx)).mpr (hC x hx)
  have hfactor (x) : q x = r x * β x := by
    dsimp [β]
    by_cases hx : r x = 0
    · simpa only [hx, zero_mul] using hzero x hx
    · field_simp
  have hdc : Continuous divF := continuous_finsetSum _
    (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  have hpath (k : ℕ) : (∫ x in Icc a b, boundaryCutoff (r x) k * divF x) =
      -(∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * β x) := by
    have hg := integral_product_divergence_box a b hab F hF
      (contDiff_boundaryCutoff (hr.of_le (by norm_num)) k) (by
        intro i y hy
        rcases hface i y hy with ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
        · rw [h1,h2]
        · rw [boundaryCutoff_zero h1, boundaryCutoff_zero h2]
          simp
        · rw [h1,h2]
          simp)
    have hflux (x : Fin (m + 1) → ℝ) :
        (∑ i, fderiv ℝ (fun y => boundaryCutoff (r y) k) x (Pi.single i 1) * F i x) =
          transitionSlope (-((k : ℝ) + 1) * r x) * β x := by
      simp_rw [fderiv_boundaryCutoff (hr.of_le (by norm_num))]
      calc
        _ = (-((k : ℝ) + 1) * deriv Real.smoothTransition (-((k : ℝ) + 1) * r x)) * q x := by
          dsimp [q]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [hfactor]; unfold transitionSlope; ring
    simpa only [hflux] using hg
  have ht := integral_boundaryCutoff_inter_tendsto (μ := volume) (K := Icc a b)
    hr.continuous hdc hdc.integrableOn_Icc
  have hz := (integral_transitionSlope_tendsto_zero hr.continuous hβ).neg
  have hz' : Tendsto (fun k : ℕ => ∫ x in Icc a b, boundaryCutoff (r x) k * divF x)
      atTop (𝓝 0) := by
    simpa only [hpath, neg_zero] using hz
  exact tendsto_nhds_unique ht hz'

theorem integral_divergence_cell_localized {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ Icc a b, r x = 0 → fderiv ℝ r x ≠ 0 ∨
      ∀ᶠ y in 𝓝 x, ∀ i, F i y = 0)
    (hzero : ∀ x, r x = 0 → ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x = 0)
    (hface : CompatibleBoxFaces a b r F) :
    (∫ x in Icc a b ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 0 := by
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  have hregq : ∀ x ∈ Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ q =ᶠ[𝓝 x] (fun _ => 0) := by
    intro x hx hz
    rcases hreg x hx hz with h | h
    · exact Or.inl h
    · apply Or.inr
      filter_upwards [h] with y hy
      simp only [q, hy, mul_zero, Finset.sum_const_zero]
  obtain ⟨C, hC0, hC⟩ := regular_or_locally_zero_compact_bound isCompact_Icc
    (hr.of_le (by norm_num)) hq hregq hzero
  exact integral_divergence_cell_of_normal_bound a b hab F hF hr hC0 hC hzero hface

end OAI.Analysis.PDE.Green
