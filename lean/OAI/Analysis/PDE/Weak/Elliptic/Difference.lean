import OAI.Analysis.PDE.Weak.CalculusWeakDifference

/-! Translation identities for actual difference quotients. -/

noncomputable section
open Set _root_.MeasureTheory
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem differenceQuotient_neg_step (v : E) (h : ℝ) (u : E → ℝ) (x : E) :
    differenceQuotient v (-h) u x = differenceQuotient v h u (x - h • v) := by
  simp only [differenceQuotient, inv_neg, neg_smul, smul_eq_mul]
  rw [sub_add_cancel]
  simp only [sub_eq_add_neg]
  ring

theorem continuous_differenceQuotient {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (v : E) (h : ℝ) {u : E → F} (hu : Continuous u) :
    Continuous (differenceQuotient v h u) := by
  exact (hu.comp (continuous_id.add continuous_const) |>.sub hu).const_smul _

theorem contDiff_differenceQuotient {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : WithTop ℕ∞} (v : E) (h : ℝ) {u : E → F}
    (hu : ContDiff ℝ k u) : ContDiff ℝ k (differenceQuotient v h u) := by
  exact ((hu.comp (contDiff_id.add contDiff_const)).sub hu).const_smul _

theorem fderiv_differenceQuotient {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (v : E) (h : ℝ) {u : E → F}
    (hu : Differentiable ℝ u) (x w : E) :
    fderiv ℝ (differenceQuotient v h u) x w =
      differenceQuotient v h (fun y ↦ fderiv ℝ u y w) x := by
  have ht : HasFDerivAt (fun y : E ↦ y + h • v) (ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).add_const _
  have hd := (((hu (x + h • v)).hasFDerivAt.comp x ht).sub
    (hu x).hasFDerivAt).const_smul (h⁻¹)
  change fderiv ℝ (h⁻¹ • ((u ∘ fun y ↦ y + h • v) - u)) x w = _
  rw [hd.fderiv]
  simp [differenceQuotient]

variable [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [μ.IsAddRightInvariant]

omit [NormedSpace ℝ E] in
theorem integral_translate_pair (a : E) (u φ : E → ℝ) :
    (∫ x, u (x + a) * φ x ∂μ) = ∫ x, u x * φ (x - a) ∂μ := by
  simpa only [add_sub_cancel_right] using
    (integral_add_right_eq_self (fun x ↦ u x * φ (x - a)) a (μ := μ))

/-- Discrete integration by parts, with exactly the two product-integrability
conditions needed to subtract the translated integrals. -/
theorem integral_differenceQuotient_mul (v : E) (h : ℝ) (u φ : E → ℝ)
    (hzero : Integrable (fun x ↦ u x * φ x) μ)
    (hshift : Integrable (fun x ↦ u (x + h • v) * φ x) μ) :
    (∫ x, differenceQuotient v h u x * φ x ∂μ) =
      -(∫ x, u x * differenceQuotient v (-h) φ x ∂μ) := by
  have hback : Integrable (fun x ↦ u x * φ (x - h • v)) μ := by
    have ht := (measurePreserving_add_right μ (-(h • v))).integrable_comp_of_integrable hshift
    change Integrable (fun x ↦ u (x + -(h • v) + h • v) * φ (x + -(h • v))) μ at ht
    simpa only [neg_add_cancel_right, sub_eq_add_neg] using ht
  calc
    (∫ x, differenceQuotient v h u x * φ x ∂μ) =
        h⁻¹ * ((∫ x, u (x + h • v) * φ x ∂μ) - ∫ x, u x * φ x ∂μ) := by
      simp only [differenceQuotient, smul_eq_mul, sub_mul, mul_assoc]
      rw [integral_const_mul, integral_sub hshift hzero]
    _ = h⁻¹ * ((∫ x, u x * φ (x - h • v) ∂μ) - ∫ x, u x * φ x ∂μ) := by
      rw [integral_translate_pair]
    _ = -(∫ x, u x * differenceQuotient v (-h) φ x ∂μ) := by
      have heq : (fun x ↦ u x * differenceQuotient v (-h) φ x) =
          fun x ↦ -(h⁻¹) * (u x * φ (x - h • v) - u x * φ x) := by
        funext x
        simp only [differenceQuotient, inv_neg, neg_smul, smul_eq_mul, sub_eq_add_neg]
        ring
      rw [heq, integral_const_mul, integral_sub hback hzero]
      ring

end OAI.Analysis.PDE.Weak
