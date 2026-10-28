import OAI.Analysis.PDE.Green.NormalCutoff
import OAI.Analysis.PDE.Green.BoundaryBound

/-! Small lateral normal flux gives a small bulk Green error on a periodic cell. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

def CompatibleBoxFaces {m : ℕ} (a b : Fin (m + 1) → ℝ)
    (r : (Fin (m + 1) → ℝ) → ℝ)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) : Prop :=
  ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    (r (i.insertNth (b i) y) = r (i.insertNth (a i) y) ∧
      F i (i.insertNth (b i) y) = F i (i.insertNth (a i) y)) ∨
    (0 ≤ r (i.insertNth (b i) y) ∧ 0 ≤ r (i.insertNth (a i) y)) ∨
    (F i (i.insertNth (b i) y) = 0 ∧ F i (i.insertNth (a i) y) = 0)

theorem cutoff_divergence_formula {m : ℕ} (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r)
    (hface : CompatibleBoxFaces a b r F) (k : ℕ) :
    (∫ x in Icc a b, boundaryCutoff (r x) k * ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) =
      ∫ x in Icc a b, normalCutoffWeight (r x) k *
        ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x := by
  have hg := integral_product_divergence_box a b hab F hF (contDiff_boundaryCutoff hr k) (by
    intro i y hy
    rcases hface i y hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [boundaryCutoff_zero h1, boundaryCutoff_zero h2]
      simp
    · rw [h1, h2]
      simp)
  have hflux (x : Fin (m + 1) → ℝ) :
      (∑ i, fderiv ℝ (fun y => boundaryCutoff (r y) k) x (Pi.single i 1) * F i x) =
        -(normalCutoffWeight (r x) k * ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x) := by
    simp_rw [fderiv_boundaryCutoff hr]
    unfold normalCutoffWeight
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hflux, integral_neg, neg_neg] using hg

theorem normalCutoffWeight_flux_bound {m : ℕ} (a b : Fin (m + 1) → ℝ)
    {r q : (Fin (m + 1) → ℝ) → ℝ} (hr : Continuous r)
    {ε C M : ℝ} (hε : 0 ≤ ε)
    (hq : ∀ x ∈ Icc a b, ‖q x‖ ≤ ε + C * ‖r x‖)
    (hM : ∀ k : ℕ, (∫ x in Icc a b, normalCutoffWeight (r x) k) ≤ M) (k : ℕ) :
    ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖ ≤
      ε * M + ∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * C := by
  have hw : Continuous (fun x => ε * normalCutoffWeight (r x) k) :=
    continuous_const.mul ((continuous_normalCutoffWeight k).comp hr)
  have hs : Continuous (fun x => transitionSlope (-((k : ℝ) + 1) * r x) * C) :=
    (continuous_transitionSlope.comp (continuous_const.mul hr)).mul continuous_const
  have hbound : ‖∫ x in Icc a b, normalCutoffWeight (r x) k * q x‖ ≤
      ∫ x in Icc a b, ε * normalCutoffWeight (r x) k +
        transitionSlope (-((k : ℝ) + 1) * r x) * C := by
    apply norm_integral_le_of_norm_le (hw.add hs).integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [norm_mul, Real.norm_of_nonneg (normalCutoffWeight_nonneg (r x) k)]
    calc
      _ ≤ normalCutoffWeight (r x) k * (ε + C * ‖r x‖) :=
        mul_le_mul_of_nonneg_left (hq x hx) (normalCutoffWeight_nonneg (r x) k)
      _ = _ := by
        dsimp only [Pi.add_apply]
        rw [← normalCutoffWeight_mul_norm]
        ring
  rw [integral_add hw.integrableOn_Icc hs.integrableOn_Icc, integral_const_mul] at hbound
  exact hbound.trans (add_le_add (mul_le_mul_of_nonneg_left (hM k) hε) le_rfl)

/-- The constant depends only on the defining function and the box; it is
independent of the vector field and of the size of its boundary flux. -/
theorem exists_small_normal_divergence_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ Icc a b, r x = 0 → fderiv ℝ r x ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ),
      (∀ i, ContDiff ℝ 1 (F i)) → ∀ ε : ℝ, 0 ≤ ε →
      (∀ x, r x = 0 → ‖∑ i, fderiv ℝ r x (Pi.single i 1) * F i x‖ ≤ ε) →
      CompatibleBoxFaces a b r F →
      ‖∫ x in (Icc a b) ∩ {x | r x < 0}, ∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ ≤ ε * M := by
  obtain ⟨M, hM0, hM⟩ := exists_uniform_normalCutoffWeight_bound a b hab hr hrne
  refine ⟨M, hM0, ?_⟩
  intro F hF ε hε hnormal hface
  let q := fun x => ∑ i, fderiv ℝ r x (Pi.single i 1) * F i x
  let divF := fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)
  have hq : ContDiff ℝ 1 q := ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul (hF i))
  obtain ⟨C, _, hC⟩ := regular_boundary_compact_bound isCompact_Icc hε
    (hr.of_le (by norm_num)) hq hrne hnormal
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
  have hright : Tendsto (fun k : ℕ => ε * M +
      ∫ x in Icc a b, transitionSlope (-((k : ℝ) + 1) * r x) * C)
      atTop (𝓝 (ε * M)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hres
  exact le_of_tendsto_of_tendsto' hnorm hright
    (fun k => normalCutoffWeight_flux_bound a b hr.continuous hε hC hM k)

end OAI.Analysis.PDE.Green
