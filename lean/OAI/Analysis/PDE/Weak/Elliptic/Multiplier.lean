import OAI.Analysis.PDE.Dirichlet.L2Coefficient

/-! Rectangular bounded coefficient fields on the actual L² spaces. -/

noncomputable section
open _root_.MeasureTheory
namespace OAI.Analysis.PDE.Weak

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure X}

theorem fieldMultiplier_memLp (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u : Lp E 2 μ) :
    MemLp (fun x ↦ A x (u x)) 2 μ := by
  apply (Lp.memLp u).of_le_mul
  · have hc : Continuous (fun p : (E →L[ℝ] F) × E ↦ p.1 p.2) := by fun_prop
    exact hc.comp_aestronglyMeasurable (hA.prodMk (Lp.aestronglyMeasurable u))
  · filter_upwards [hM] with x hx
    exact ((A x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

def fieldMultiplier (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u : Lp E 2 μ) : Lp F 2 μ :=
  (fieldMultiplier_memLp A hA hM u).toLp (fun x ↦ A x (u x))

theorem fieldMultiplier_ae (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u : Lp E 2 μ) :
    fieldMultiplier A hA hM u =ᵐ[μ] fun x ↦ A x (u x) :=
  (fieldMultiplier_memLp A hA hM u).coeFn_toLp

theorem norm_fieldMultiplier_le (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u : Lp E 2 μ) :
    ‖fieldMultiplier A hA hM u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldMultiplier_ae A hA hM u, hM] with x hx hAx
  rw [hx]
  exact ((A x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right hAx (norm_nonneg _))

def fieldMultiplierLinear (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) : Lp E 2 μ →ₗ[ℝ] Lp F 2 μ where
  toFun := fieldMultiplier A hA hM
  map_add' u w := by
    apply Lp.ext
    filter_upwards [fieldMultiplier_ae A hA hM (u + w), fieldMultiplier_ae A hA hM u,
      fieldMultiplier_ae A hA hM w, Lp.coeFn_add u w,
      Lp.coeFn_add (fieldMultiplier A hA hM u) (fieldMultiplier A hA hM w)]
      with x hsum hu hw hadd hout
    simp only [hsum, hout, hu, hw, hadd, Pi.add_apply, map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [fieldMultiplier_ae A hA hM (c • u), fieldMultiplier_ae A hA hM u,
      Lp.coeFn_smul c u, Lp.coeFn_smul c (fieldMultiplier A hA hM u)]
      with x hsmul hu hin hout
    simp only [hsmul, hout, hu, hin, Pi.smul_apply, map_smul, RingHom.id_apply]

def fieldMultiplierCLM (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) : Lp E 2 μ →L[ℝ] Lp F 2 μ :=
  (fieldMultiplierLinear A hA hM).mkContinuous M (norm_fieldMultiplier_le A hA hM)

theorem fieldMultiplierCLM_ae (A : X → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    {M : ℝ} (hM : ∀ᵐ x ∂μ, ‖A x‖ ≤ M) (u : Lp E 2 μ) :
    fieldMultiplierCLM A hA hM u =ᵐ[μ] fun x ↦ A x (u x) :=
  fieldMultiplier_ae A hA hM u

end OAI.Analysis.PDE.Weak
