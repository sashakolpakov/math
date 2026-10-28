import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open _root_.MeasureTheory Filter
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}

theorem coefficient_memLp (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (f : Lp E 2 μ) :
    MemLp (fun x ↦ A x (f x)) 2 μ := by
  apply (Lp.memLp f).of_le_mul
  · have hc : Continuous (fun p : (E →L[ℝ] E) × E ↦ p.1 p.2) := by fun_prop
    exact hc.comp_aestronglyMeasurable (hA.prodMk (Lp.aestronglyMeasurable f))
  · filter_upwards [hAM] with x hx
    exact ((A x).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

/-- Multiplication by a measurable, essentially bounded coefficient field
on the actual L² space of vector fields. -/
def coefficientLp (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (f : Lp E 2 μ) : Lp E 2 μ :=
  (coefficient_memLp A hA hAM f).toLp (fun x ↦ A x (f x))

theorem coefficientLp_ae (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (f : Lp E 2 μ) :
    coefficientLp A hA hAM f =ᵐ[μ] fun x ↦ A x (f x) :=
  (coefficient_memLp A hA hAM f).coeFn_toLp

theorem norm_coefficientLp_le (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (_ : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (f : Lp E 2 μ) :
    ‖coefficientLp A hA hAM f‖ ≤ M * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coefficientLp_ae A hA hAM f, hAM] with x hx hAx
  rw [hx]
  exact ((A x).le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))

def coefficientLpLinear (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ where
  toFun := coefficientLp A hA hAM
  map_add' f g := by
    ext1
    filter_upwards [coefficientLp_ae A hA hAM (f + g), coefficientLp_ae A hA hAM f,
      coefficientLp_ae A hA hAM g, Lp.coeFn_add f g,
      Lp.coeFn_add (coefficientLp A hA hAM f) (coefficientLp A hA hAM g)] with x hsum hf hg hadd hout
    simp only [hsum, hout, hf, hg, hadd, Pi.add_apply, map_add]
  map_smul' c f := by
    ext1
    filter_upwards [coefficientLp_ae A hA hAM (c • f), coefficientLp_ae A hA hAM f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (coefficientLp A hA hAM f)] with x hsmul hf hin hout
    simp only [hsmul, hout, hf, hin, Pi.smul_apply, map_smul, RingHom.id_apply]

def coefficientLpCLM (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (coefficientLpLinear A hA hAM).mkContinuous M (norm_coefficientLp_le A hA hM hAM)

theorem coefficientLpCLM_ae (A : X → E →L[ℝ] E) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : 0 ≤ M) (hAM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (f : Lp E 2 μ) :
    coefficientLpCLM A hA hM hAM f =ᵐ[μ] fun x ↦ A x (f x) :=
  coefficientLp_ae A hA hAM f

end OAI.Analysis.PDE.Dirichlet
