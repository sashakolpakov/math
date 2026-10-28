import OAI.Analysis.PDE.Weak.Elliptic.DifferenceBound
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section
open Set _root_.MeasureTheory Filter
open scoped Topology
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
theorem tendsto_differenceQuotient (φ : X → V) (hφ : Differentiable ℝ φ)
    (v x : X) {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ differenceQuotient v (s n) φ x) atTop
      (𝓝 (fderiv ℝ φ x v)) := by
  have hp : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hd : HasDerivAt (fun t : ℝ ↦ φ (x + t • v)) (fderiv ℝ φ x v) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def] using!
      (hφ (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt 0 hp
  have hs' : Tendsto s atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hs0⟩
  simpa only [slope, sub_zero, zero_smul, add_zero, Function.comp_def, differenceQuotient,
    vsub_eq_sub]
    using hd.tendsto_slope.comp hs'

variable [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]

/-- Difference quotients of a smooth test converge inside their pairing
with an actual L¹ field, by domination from the bounded derivative. -/
theorem tendsto_integral_inner_differenceQuotient (μ : Measure X) (u φ : X → V)
    (hu : Integrable u μ) (hφ : ContDiff ℝ 1 φ) (v : X) {M : ℝ}
    (hM : ∀ x, ‖fderiv ℝ φ x‖ ≤ M) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0) :
    Tendsto (fun n ↦ ∫ x, inner ℝ (u x) (differenceQuotient v (s n) φ x) ∂μ) atTop
      (𝓝 (∫ x, inner ℝ (u x) (fderiv ℝ φ x v) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x‖ * (M * ‖v‖))
  · intro n
    exact hu.aestronglyMeasurable.inner
      (continuous_differenceQuotient v (s n) hφ.continuous).aestronglyMeasurable
  · exact hu.norm.mul_const _
  · intro n
    apply Eventually.of_forall
    intro x
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_differenceQuotient_le φ hφ v x (hs0 n) (fun t _ ↦ hM _)) (norm_nonneg _))
  · apply Eventually.of_forall
    intro x
    exact tendsto_const_nhds.inner (tendsto_differenceQuotient φ
      (hφ.differentiable one_ne_zero) v x hs hs0)

end OAI.Analysis.PDE.Weak
