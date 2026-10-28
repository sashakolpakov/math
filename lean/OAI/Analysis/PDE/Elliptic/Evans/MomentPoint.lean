import OAI.Analysis.PDE.Elliptic.Evans.CommonPoint

open Set _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

/-- A common pointwise bound obtained from the small-exponent moments.
The multiplicative constant is independent of the scale and the measure. -/
theorem finite_rpow_moments_common_point {X I : Type*} [MeasurableSpace X]
    [Fintype I] [Nonempty I] {p C : ℝ} (hp : 0 < p) (hC : 0 < C) :
    ∃ K > 0, ∀ (μ : Measure X) (S : Set X), MeasurableSet S → μ S ≠ 0 → μ S ≠ ∞ →
      ∀ D : ℝ, 0 < D → ∀ v : I → X → ℝ,
      (∀ i, Measurable (v i)) → (∀ i x, x ∈ S → 0 ≤ v i x) →
      (∀ i, (∫⁻ x in S, ENNReal.ofReal (v i x) ^ p ∂μ) ≤
        ENNReal.ofReal (C * D ^ p) * μ S) →
      ∃ x ∈ S, ∀ i, v i x ≤ K * D := by
  let N : ℝ := Fintype.card I
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card I)
  let K := (2 * N * C) ^ p⁻¹
  have hK : 0 < K := Real.rpow_pos_of_pos (by positivity) _
  have hKpow : K ^ p = 2 * N * C := Real.rpow_inv_rpow (by positivity) hp.ne'
  refine ⟨K, hK, ?_⟩
  intro μ S hS hμ0 hμfin D hD v hv hnonneg hbound
  have hf (i : I) : Measurable (fun x ↦ ENNReal.ofReal (v i x) ^ p) := by
    fun_prop
  obtain ⟨x, hx, hpoint⟩ := finite_moments_common_point μ hS hμ0 hμfin
    (fun i x ↦ ENNReal.ofReal (v i x) ^ p) hf (by positivity : 0 < C * D ^ p) hbound
  refine ⟨x, hx, fun i ↦ ?_⟩
  have hi := hpoint i
  rw [ENNReal.ofReal_rpow_of_nonneg (hnonneg i x hx) hp.le] at hi
  have hreal : (v i x) ^ p < 2 * N * (C * D ^ p) := by
    by_contra! hn
    exact (not_le_of_gt hi) (ENNReal.ofReal_le_ofReal hn)
  apply (Real.rpow_le_rpow_iff (hnonneg i x hx) (mul_nonneg hK.le hD.le) hp).mp
  rw [Real.mul_rpow hK.le hD.le, hKpow]
  nlinarith

end OAI.Analysis.PDE.Elliptic
