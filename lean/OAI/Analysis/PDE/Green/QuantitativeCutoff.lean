import OAI.Analysis.PDE.Green.NormalCutoff

/-! Explicit geometric constants for the normal-cutoff integral estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory

def boxVolume {m : ℕ} (a b : Fin m → ℝ) : ℝ := ∫ _x in Icc a b, (1 : ℝ)

def boxBoundaryVolume {m : ℕ} (a b : Fin (m + 1) → ℝ) : ℝ :=
  ∑ i : Fin (m + 1), (boxVolume (a ∘ i.succAbove) (b ∘ i.succAbove) +
    boxVolume (a ∘ i.succAbove) (b ∘ i.succAbove))

theorem integral_norm_le_boxVolume {m : ℕ} (a b : Fin m → ℝ)
    {f : (Fin m → ℝ) → ℝ} (hf : Continuous f) {L : ℝ}
    (hL : ∀ x ∈ Icc a b, ‖f x‖ ≤ L) :
    (∫ x in Icc a b, ‖f x‖) ≤ L * boxVolume a b := by
  unfold boxVolume
  rw [← integral_const_mul]
  apply setIntegral_mono_on hf.norm.integrableOn_Icc
    (continuous_const : Continuous (fun _ : Fin m → ℝ => L * 1)).integrableOn_Icc measurableSet_Icc
  intro x hx
  simpa only [mul_one] using hL x hx

theorem boxBoundaryNorm_le_boxBoundaryVolume {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, Continuous (F i))
    {L : ℝ} (hL : ∀ i x, x ∈ Icc a b → ‖F i x‖ ≤ L) :
    boxBoundaryNorm a b F ≤ L * boxBoundaryVolume a b := by
  unfold boxBoundaryNorm boxBoundaryVolume
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [mul_add]
  apply add_le_add
  · apply integral_norm_le_boxVolume _ _ ((hF i).comp (continuous_insertNth_fixed i (b i)))
    intro y hy
    apply hL
    exact Fin.insertNth_mem_Icc.2 ⟨⟨hab i, le_rfl⟩, hy⟩
  · apply integral_norm_le_boxVolume _ _ ((hF i).comp (continuous_insertNth_fixed i (a i)))
    intro y hy
    apply hL
    exact Fin.insertNth_mem_Icc.2 ⟨⟨le_rfl, hab i⟩, hy⟩

/-- A numerical normal-cutoff bound from a transverse-field lower bound and
upper bounds on the field, its divergence, and the defining function. -/
theorem normalCutoffWeight_integral_bound_explicit {m : ℕ}
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 1 r)
    {c C L D R : ℝ} (hc : 0 < c) (hC : ∀ t, ‖transitionSlope t‖ ≤ C)
    (hmin : ∀ x ∈ Icc a b, c ≤ (∑ i, fderiv ℝ r x (Pi.single i 1) * F i x) + r x ^ 2)
    (hL : ∀ i x, x ∈ Icc a b → ‖F i x‖ ≤ L)
    (hD : ∀ x ∈ Icc a b, ‖∑ i, fderiv ℝ (F i) x (Pi.single i 1)‖ ≤ D)
    (hR : ∀ x ∈ Icc a b, ‖r x‖ ≤ R) (k : ℕ) :
    (∫ x in Icc a b, normalCutoffWeight (r x) k) ≤
      (L * boxBoundaryVolume a b + D * boxVolume a b + C * R * boxVolume a b) / c := by
  have hC0 : 0 ≤ C := (norm_nonneg (transitionSlope 0)).trans (hC 0)
  have hfield := boxBoundaryNorm_le_boxBoundaryVolume a b hab F
    (fun i => (hF i).continuous) hL
  have hdiv := integral_norm_le_boxVolume a b
    (continuous_finsetSum _ (fun i _ => continuous_directional (hF i) (Pi.single i 1))) hD
  have hdef := integral_norm_le_boxVolume a b hr.continuous hR
  apply (normalCutoffWeight_integral_bound a b hab F hF hr hc hC hmin k).trans
  apply div_le_div_of_nonneg_right _ hc.le
  nlinarith [mul_le_mul_of_nonneg_left hdef hC0]

end OAI.Analysis.PDE.Green
