import OAI.Analysis.PDE.Elliptic.HarnackSource

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

theorem exists_lt_of_setLIntegral_lt_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S) (f : X → ℝ≥0∞)
    {a : ℝ≥0∞} (h : (∫⁻ x in S, f x ∂μ) < a * μ S) :
    ∃ x ∈ S, f x < a := by
  by_contra! hn
  have hlo : a * μ S ≤ ∫⁻ x in S, f x ∂μ := by
    calc
      _ = ∫⁻ _x in S, a ∂μ := by simp
      _ ≤ _ := lintegral_mono_ae (by
        filter_upwards [ae_restrict_mem hS] with x hx
        exact hn x hx)
  exact (not_lt_of_ge hlo) h

/-- Finitely many moment bounds have a common good point. This supplies
the simultaneous direction selection in the oscillation argument. -/
theorem finite_moments_common_point {X I : Type*} [MeasurableSpace X]
    [Fintype I] [Nonempty I] (μ : Measure X) {S : Set X}
    (hS : MeasurableSet S) (hμ0 : μ S ≠ 0) (hμfin : μ S ≠ ∞)
    (f : I → X → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    {A : ℝ} (hA : 0 < A)
    (hbound : ∀ i, (∫⁻ x in S, f i x ∂μ) ≤ ENNReal.ofReal A * μ S) :
    ∃ x ∈ S, ∀ i, f i x < ENNReal.ofReal (2 * (Fintype.card I : ℝ) * A) := by
  classical
  let N : ℝ := Fintype.card I
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  have hsum : (∫⁻ x in S, ∑ i, f i x ∂μ) ≤ ENNReal.ofReal (N * A) * μ S := by
    calc
      _ = ∑ i, ∫⁻ x in S, f i x ∂μ := by
        exact lintegral_finsetSum _ (fun i _ ↦ hf i)
      _ ≤ ∑ _i : I, ENNReal.ofReal A * μ S := Finset.sum_le_sum (fun i _ ↦ hbound i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        rw [ENNReal.ofReal_mul hN.le]
        congr 2
        simp [N]
  have hstrict : ENNReal.ofReal (N * A) * μ S <
      ENNReal.ofReal (2 * N * A) * μ S := by
    apply (ENNReal.toReal_lt_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμfin)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ N * A),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * N * A)]
    exact mul_lt_mul_of_pos_right (by nlinarith) (ENNReal.toReal_pos hμ0 hμfin)
  obtain ⟨x, hx, hxsum⟩ := exists_lt_of_setLIntegral_lt_const μ hS
    (fun x ↦ ∑ i, f i x) (hsum.trans_lt hstrict)
  refine ⟨x, hx, fun i ↦ ?_⟩
  exact (Finset.single_le_sum (fun j _ ↦ bot_le) (Finset.mem_univ i)).trans_lt hxsum

end OAI.Analysis.PDE.Elliptic
