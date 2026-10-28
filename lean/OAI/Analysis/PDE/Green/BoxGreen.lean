import OAI.Analysis.PDE.Green.RegularBoundary
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! Green identities on a periodic cell: opposite faces cancel before the
defining-function cutoff is removed. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem integral_divergence_box_zero {m : ℕ} (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      F i (i.insertNth (b i) y) = F i (i.insertNth (a i) y)) :
    (∫ x in Icc a b, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 0 := by
  have hc : Continuous (fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) :=
    continuous_finsetSum _ (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  rw [integral_divergence_of_hasFDerivAt_off_countable' a b hab F
    (fun i => fderiv ℝ (F i)) ∅ Set.countable_empty
    (fun i => (hF i).continuous.continuousOn)
    (fun x _ i => ((hF i).differentiable (by norm_num) x).hasFDerivAt)
    hc.integrableOn_Icc]
  apply Finset.sum_eq_zero
  intro i _
  rw [setIntegral_congr_fun measurableSet_Icc (hface i), sub_self]

theorem product_divergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] (d : I → E) (F : I → E → ℝ)
    (hF : ∀ i, ContDiff ℝ 1 (F i)) {φ : E → ℝ} (hφ : ContDiff ℝ 1 φ) (x : E) :
    (∑ i, fderiv ℝ (fun y => φ y * F i y) x (d i)) =
      φ x * (∑ i, fderiv ℝ (F i) x (d i)) +
        ∑ i, fderiv ℝ φ x (d i) * F i x := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change (fderiv ℝ (φ * F i) x) (d i) = _
  rw [fderiv_mul (hφ.differentiable (by norm_num) x)
    ((hF i).differentiable (by norm_num) x)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem integral_product_divergence_box {m : ℕ} (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      φ (i.insertNth (b i) y) * F i (i.insertNth (b i) y) =
        φ (i.insertNth (a i) y) * F i (i.insertNth (a i) y)) :
    (∫ x in Icc a b, φ x * ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) =
      -(∫ x in Icc a b, ∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x) := by
  have hz := integral_divergence_box_zero a b hab (fun i y => φ y * F i y)
    (fun i => hφ.mul (hF i)) hface
  simp_rw [product_divergence (fun i => Pi.single i 1) F hF hφ] at hz
  have hleft : Continuous (fun x => φ x * ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) :=
    hφ.continuous.mul (continuous_finsetSum _
      (fun i _ => continuous_directional (hF i) (Pi.single i 1)))
  have hright : Continuous (fun x => ∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x) :=
    continuous_finsetSum _ (fun i _ =>
      (continuous_directional hφ (Pi.single i 1)).mul (hF i).continuous)
  rw [integral_add hleft.integrableOn_Icc hright.integrableOn_Icc] at hz
  linarith

theorem integral_boundaryCutoff_inter_tendsto
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} {K : Set E} {r f : E → ℝ}
    (hr : Continuous r) (hf : Continuous f) (hfi : IntegrableOn f K μ) :
    Tendsto (fun k : ℕ => ∫ x in K, boundaryCutoff (r x) k * f x ∂μ) atTop
      (𝓝 (∫ x in K ∩ {x | r x < 0}, f x ∂μ)) := by
  have hN : MeasurableSet {x | r x < 0} := (isOpen_lt hr continuous_const).measurableSet
  have ht : Tendsto (fun k : ℕ => ∫ x in K, boundaryCutoff (r x) k * f x ∂μ) atTop
      (𝓝 (∫ x in K, {x | r x < 0}.indicator f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    · intro k
      exact ((Real.smoothTransition.continuous.comp (continuous_const.mul hr)).mul hf).aestronglyMeasurable
    · exact hfi.norm
    · intro k
      apply Filter.Eventually.of_forall
      intro x
      rw [norm_mul]
      have hc : ‖boundaryCutoff (r x) k‖ ≤ 1 := by
        unfold boundaryCutoff
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        exact Real.smoothTransition.le_one _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f x))
    · apply Filter.Eventually.of_forall
      intro x
      by_cases hx : r x < 0
      · rw [Set.indicator_of_mem (show x ∈ {x | r x < 0} from hx)]
        simpa only [one_mul] using (boundaryCutoff_tendsto hx).mul
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
      · rw [Set.indicator_of_notMem (show x ∉ {x | r x < 0} from hx)]
        simpa only [boundaryCutoff_zero (le_of_not_gt hx), zero_mul]
          using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  simpa only [integral_indicator hN, Measure.restrict_restrict hN, Set.inter_comm] using ht

/-- A periodic cell may have matching opposite faces, faces outside the
sublevel, or zero flux on both faces. Its actual tangential divergence integrates
to zero without any boundedness assumption on the full sublevel set. -/
theorem integral_divergence_cell_sublevel_zero {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 → ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x = 0)
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (r (i.insertNth (b i) y) = r (i.insertNth (a i) y) ∧
        F i (i.insertNth (b i) y) = F i (i.insertNth (a i) y)) ∨
      (0 ≤ r (i.insertNth (b i) y) ∧ 0 ≤ r (i.insertNth (a i) y)) ∨
      (F i (i.insertNth (b i) y) = 0 ∧ F i (i.insertNth (a i) y) = 0)) :
    (∫ x in Icc a b ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = 0 := by
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let β := fun x => q x / r x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  obtain ⟨C, hC0, hC⟩ := regular_zero_compact_bound isCompact_Icc
    (hr.of_le (by norm_num)) hq hrne hzero
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

end OAI.Analysis.PDE.Green
