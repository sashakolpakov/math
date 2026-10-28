import OAI.Analysis.PDE.Green.BoxGreen

/-! Quantitative Green estimates on a box, prior to the lateral cutoff limit. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem continuous_insertNth_fixed {m : ℕ} (i : Fin (m + 1)) (t : ℝ) :
    Continuous (fun y : Fin m → ℝ => (i.insertNth t y : Fin (m + 1) → ℝ)) := by
  apply continuous_pi
  intro j
  rcases eq_or_ne j i with rfl | hji
  · simpa using (continuous_const : Continuous (fun _ : Fin m → ℝ => t))
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
    simpa using (continuous_apply k : Continuous (fun x : Fin m → ℝ => x k))

def boxBoundaryNorm {m : ℕ} (a b : Fin (m + 1) → ℝ)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) : ℝ :=
  ∑ i, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), ‖F i (i.insertNth (b i) y)‖) +
    ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove), ‖F i (i.insertNth (a i) y)‖)

theorem norm_integral_mul_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f φ : E → ℝ} (hf : Integrable f μ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x, φ x * f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  apply norm_integral_le_of_norm_le hf.norm
  apply Filter.Eventually.of_forall
  intro x
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hφ x) (norm_nonneg (f x))

theorem box_boundary_product_norm_le {m : ℕ} (a b : Fin (m + 1) → ℝ)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ)
    (hF : ∀ i, Continuous (F i)) {φ : (Fin (m + 1) → ℝ) → ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∑ i, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      φ (i.insertNth (b i) y) * F i (i.insertNth (b i) y)) -
      ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        φ (i.insertNth (a i) y) * F i (i.insertNth (a i) y))‖ ≤ boxBoundaryNorm a b F := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sub_le _ _).trans
  exact add_le_add
    (norm_integral_mul_le ((hF i).comp (continuous_insertNth_fixed i (b i))).integrableOn_Icc
      (fun y => hφ _))
    (norm_integral_mul_le ((hF i).comp (continuous_insertNth_fixed i (a i))).integrableOn_Icc
      (fun y => hφ _))

/-- Bounded scalar multipliers give a quantitative Green estimate with explicit
box-face and bulk terms. This estimate does not assume tangency on a lateral boundary. -/
theorem integral_normal_derivative_box_bound {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {φ : (Fin (m + 1) → ℝ) → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφnorm : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x in Icc a b, ∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x‖ ≤
      boxBoundaryNorm a b F + ∫ x in Icc a b, ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ := by
  have hdiv : Continuous (fun x => ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) :=
    continuous_finsetSum _ (fun i _ => continuous_directional (hF i) (Pi.single i 1))
  have hnormal : Continuous (fun x => ∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x) :=
    continuous_finsetSum _ (fun i _ =>
      (continuous_directional hφ (Pi.single i 1)).mul (hF i).continuous)
  have hleft : Continuous (fun x => φ x * ∑ i, fderiv ℝ (F i) x (Pi.single i 1)) :=
    hφ.continuous.mul hdiv
  have hp (i : Fin (m + 1)) : ContDiff ℝ 1 (fun x => φ x * F i x) := hφ.mul (hF i)
  have hdp : Continuous (fun x => ∑ i,
      fderiv ℝ (fun y => φ y * F i y) x (Pi.single i 1)) :=
    continuous_finsetSum _ (fun i _ => continuous_directional (hp i) (Pi.single i 1))
  have he := integral_divergence_of_hasFDerivAt_off_countable' a b hab
    (fun i x => φ x * F i x) (fun i => fderiv ℝ (fun x => φ x * F i x))
    ∅ Set.countable_empty (fun i => (hp i).continuous.continuousOn)
    (fun x _ i => ((hp i).differentiable (by norm_num) x).hasFDerivAt)
    hdp.integrableOn_Icc
  simp_rw [product_divergence (fun i => Pi.single i 1) F hF hφ] at he
  rw [integral_add hleft.integrableOn_Icc hnormal.integrableOn_Icc] at he
  have hbnd := box_boundary_product_norm_le a b F (fun i => (hF i).continuous) hφnorm
  have hbulk := norm_integral_mul_le (μ := volume.restrict (Icc a b))
    hdiv.integrableOn_Icc hφnorm
  have hsum : (∫ x in Icc a b, ∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x) =
      (∑ i, ((∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
        φ (i.insertNth (b i) y) * F i (i.insertNth (b i) y)) -
        ∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
          φ (i.insertNth (a i) y) * F i (i.insertNth (a i) y))) -
      ∫ x in Icc a b, φ x * ∑ i, fderiv ℝ (F i) x (Pi.single i 1) := by linarith
  rw [hsum]
  exact (norm_sub_le _ _).trans (add_le_add hbnd hbulk)

end OAI.Analysis.PDE.Green
