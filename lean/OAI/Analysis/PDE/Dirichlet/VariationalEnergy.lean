import OAI.Analysis.PDE.Dirichlet.L2Coefficient
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

open _root_.MeasureTheory Filter
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

/-- The bounded bilinear energy associated with a measurable real
coefficient field, on actual L² vector fields. -/
def coefficientEnergy (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) :
    Lp E 2 μ →L[ℝ] Lp E 2 μ →L[ℝ] ℝ :=
  (((innerSL ℝ (E := Lp E 2 μ)).flip).comp (coefficientLpCLM A hA hM hAM)).flip

theorem coefficientEnergy_apply (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (g h : Lp E 2 μ) :
    coefficientEnergy A hA hM hAM g h = inner ℝ g (coefficientLpCLM A hA hM hAM h) := rfl

theorem coefficientEnergy_eq_integral (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (g h : Lp E 2 μ) :
    coefficientEnergy A hA hM hAM g h = ∫ x, inner ℝ (g x) (A x (h x)) ∂μ := by
  rw [coefficientEnergy_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coefficientLpCLM_ae A hA hM hAM h] with x hx
  rw [hx]

theorem integrable_coefficient_pairing (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (g h : Lp E 2 μ) :
    Integrable (fun x ↦ inner ℝ (g x) (A x (h x))) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) g (coefficientLpCLM A hA hM hAM h)).congr
  filter_upwards [coefficientLpCLM_ae A hA hM hAM h] with x hx
  rw [hx]

theorem norm_coefficientEnergy_apply_le (A : X → E →L[ℝ] E)
    (hA : AEStronglyMeasurable A μ) {M : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (g h : Lp E 2 μ) :
    ‖coefficientEnergy A hA hM hAM g h‖ ≤ M * ‖g‖ * ‖h‖ := by
  rw [coefficientEnergy_apply]
  calc
    _ ≤ ‖g‖ * ‖coefficientLpCLM A hA hM hAM h‖ := norm_inner_le_norm _ _
    _ ≤ ‖g‖ * (M * ‖h‖) := mul_le_mul_of_nonneg_left
      (norm_coefficientLp_le A hA hM hAM h) (norm_nonneg _)
    _ = _ := by ring

/-- Pointwise uniform ellipticity gives the exact L² coercivity constant. -/
theorem coefficientEnergy_lower_bound (A : X → E →L[ℝ] E)
    (hA : AEStronglyMeasurable A μ) {M lam : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M)
    (hell : ∀ᵐ x ∂μ, ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v))
    (g : Lp E 2 μ) : lam * ‖g‖ ^ 2 ≤ coefficientEnergy A hA hM hAM g g := by
  rw [coefficientEnergy_eq_integral]
  calc
    lam * ‖g‖ ^ 2 = ∫ x, lam * inner ℝ (g x) (g x) ∂μ := by
      rw [integral_const_mul, ← L2.inner_def, real_inner_self_eq_norm_sq]
    _ ≤ ∫ x, inner ℝ (g x) (A x (g x)) ∂μ := by
      apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) g g).const_mul lam)
        (integrable_coefficient_pairing A hA hM hAM g g)
      filter_upwards [hell] with x hx
      simpa only [real_inner_self_eq_norm_sq] using hx (g x)

theorem coefficientEnergy_isCoercive (A : X → E →L[ℝ] E)
    (hA : AEStronglyMeasurable A μ) {M lam : ℝ} (hM : 0 ≤ M)
    (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂μ, ∀ v : E, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) :
    IsCoercive (coefficientEnergy A hA hM hAM) := by
  refine ⟨lam, hlam, ?_⟩
  intro g
  simpa only [pow_two, mul_assoc] using
    coefficientEnergy_lower_bound A hA hM hAM hell g

end OAI.Analysis.PDE.Dirichlet
