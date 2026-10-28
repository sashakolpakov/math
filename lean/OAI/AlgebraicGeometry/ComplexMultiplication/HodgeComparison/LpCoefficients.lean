import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-! # Lp Coefficients -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction

noncomputable section

/-! Bounded measurable operator coefficients acting on actual Lp functions. -/

open _root_.MeasureTheory
open scoped ENNReal

variable {α 𝕜 E : Type*} [MeasurableSpace α] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {μ : Measure α} {p : ℝ≥0∞}

theorem boundedField_memLp (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u : Lp E p μ) :
    MemLp (fun x => A x (u x)) p μ := by
  apply (Lp.memLp u).of_le_mul
    ((ContinuousLinearMap.id 𝕜 (E →L[𝕜] E)).aestronglyMeasurable_comp₂ hA (Lp.aestronglyMeasurable u))
  filter_upwards [hC] with x hx
  exact (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def boundedFieldApply (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u : Lp E p μ) : Lp E p μ :=
  (boundedField_memLp A hA hC u).toLp (fun x => A x (u x))

theorem boundedFieldApply_coe (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u : Lp E p μ) :
    ∀ᵐ x ∂μ, boundedFieldApply A hA hC u x = A x (u x) :=
  MemLp.coeFn_toLp (boundedField_memLp A hA hC u)

def boundedFieldLinear (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : Lp E p μ →ₗ[𝕜] Lp E p μ where
  toFun := boundedFieldApply A hA hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [boundedFieldApply_coe A hA hC (u + v),
      boundedFieldApply_coe A hA hC u, boundedFieldApply_coe A hA hC v,
      Lp.coeFn_add u v, Lp.coeFn_add (boundedFieldApply A hA hC u) (boundedFieldApply A hA hC v)]
      with x huv hu hv hadd hout
    simp only [huv, hadd, Pi.add_apply, map_add, hout, hu, hv]
  map_smul' r u := by
    apply Lp.ext
    filter_upwards [boundedFieldApply_coe A hA hC (r • u),
      boundedFieldApply_coe A hA hC u, Lp.coeFn_smul r u,
      Lp.coeFn_smul r (boundedFieldApply A hA hC u)] with x hru hu hsmul hout
    simp only [RingHom.id_apply, hru, hsmul, Pi.smul_apply, map_smul, hout, hu]

theorem boundedFieldLinear_norm_le (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u : Lp E p μ) :
    ‖boundedFieldLinear A hA hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedFieldApply_coe A hA hC u, hC] with x hu hx
  change ‖boundedFieldApply A hA hC u x‖ ≤ C * ‖u x‖
  rw [hu]
  exact (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

variable [Fact (1 ≤ p)]

def boundedFieldLp (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) : Lp E p μ →L[𝕜] Lp E p μ :=
  (boundedFieldLinear (p := p) A hA hC).mkContinuous C
    (fun u => boundedFieldLinear_norm_le A hA hC u)

theorem boundedFieldLp_coe (A : α → E →L[𝕜] E) (hA : AEStronglyMeasurable A μ)
    {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖A x‖ ≤ C) (u : Lp E p μ) :
    ∀ᵐ x ∂μ, boundedFieldLp A hA hC u x = A x (u x) :=
  boundedFieldApply_coe A hA hC u

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients.CM.Construction
