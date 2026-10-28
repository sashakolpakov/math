import OAI.Analysis.PDE.Weak.Elliptic.DifferenceBound
import OAI.Analysis.PDE.Variational.CellL2

noncomputable section
open Set _root_.MeasureTheory
namespace OAI.Analysis.PDE.Weak

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (μ : Measure X) [μ.IsAddRightInvariant]

def translateL2 (a : X) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ x + a)
    (measurePreserving_add_right μ a)).toContinuousLinearMap

def differenceQuotientL2 (v : X) (h : ℝ) : Lp V 2 μ →L[ℝ] Lp V 2 μ :=
  h⁻¹ • (translateL2 μ (h • v) - ContinuousLinearMap.id ℝ (Lp V 2 μ))

omit [NormedSpace ℝ X] in
theorem coe_translateL2 (a : X) (u : Lp V 2 μ) :
    translateL2 μ a u =ᵐ[μ] fun x ↦ u (x + a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right μ a)

omit [NormedSpace ℝ X] in
theorem norm_translateL2 (a : X) (u : Lp V 2 μ) : ‖translateL2 μ a u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_add_right μ a)

theorem coe_differenceQuotientL2 (v : X) (h : ℝ) (u : Lp V 2 μ) :
    differenceQuotientL2 μ v h u =ᵐ[μ] differenceQuotient v h u := by
  change (h⁻¹ • (translateL2 μ (h • v) u - u) : Lp V 2 μ) =ᵐ[μ] _
  filter_upwards [Lp.coeFn_smul h⁻¹ (translateL2 μ (h • v) u - u),
    Lp.coeFn_sub (translateL2 μ (h • v) u) u, coe_translateL2 μ (h • v) u] with x hx hy hz
  simp only [Pi.smul_apply, Pi.sub_apply] at hx hy
  rw [hx, hy, hz]
  rfl

theorem norm_differenceQuotientL2_le (v : X) (h : ℝ) (u : Lp V 2 μ) :
    ‖differenceQuotientL2 μ v h u‖ ≤ (2 * |h⁻¹|) * ‖u‖ := by
  change ‖h⁻¹ • (translateL2 μ (h • v) u - u)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  have ht := norm_sub_le (translateL2 μ (h • v) u) u
  rw [norm_translateL2] at ht
  nlinarith [mul_le_mul_of_nonneg_left ht (abs_nonneg h⁻¹)]

theorem memLp_differenceQuotient (v : X) (h : ℝ) {u : X → V}
    (hu : MemLp u 2 μ) : MemLp (differenceQuotient v h u) 2 μ :=
  ((hu.comp_measurePreserving (measurePreserving_add_right μ (h • v))).sub hu).const_smul h⁻¹

theorem differenceQuotientL2_toLp (v : X) (h : ℝ) {u : X → V}
    (hu : MemLp u 2 μ) :
    differenceQuotientL2 μ v h (hu.toLp u) =
      (memLp_differenceQuotient μ v h hu).toLp (differenceQuotient v h u) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right μ (h • v)).quasiMeasurePreserving.ae
    hu.coeFn_toLp
  filter_upwards [coe_differenceQuotientL2 μ v h (hu.toLp u), hu.coeFn_toLp, ht,
    (memLp_differenceQuotient μ v h hu).coeFn_toLp]
    with x hx hy hz hw
  rw [hx, hw]
  simp only [differenceQuotient, hy, hz]

variable [CompleteSpace V] [SFinite μ]
  [SecondCountableTopology X]

omit [SecondCountableTopology X] in
theorem norm_differenceQuotientL2_smooth_le {u : X → V}
    (hu : ContDiff ℝ 1 u) (hu2 : MemLp u 2 μ) (v : X) {h : ℝ} (hh : h ≠ 0)
    (hd2 : MemLp (fun x ↦ fderiv ℝ u x v) 2 μ) :
    ‖differenceQuotientL2 μ v h (hu2.toLp u)‖ ≤
      ‖hd2.toLp (fun x ↦ fderiv ℝ u x v)‖ := by
  let hq := memLp_differenceQuotient μ v h hu2
  have hqs : Integrable (fun x ↦ ‖differenceQuotient v h u x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).mp hq
  have hds : Integrable (fun x ↦ ‖fderiv ℝ u x v‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).mp hd2
  have he := lintegral_differenceQuotient_sq_le μ u hu v hh
  rw [← ofReal_integral_eq_lintegral_ofReal hqs (Filter.Eventually.of_forall fun x ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hds (Filter.Eventually.of_forall fun x ↦ sq_nonneg _)] at he
  have hi := (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ sq_nonneg _)).mp he
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [differenceQuotientL2_toLp, OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral,
    OAI.Analysis.PDE.Variational.norm_sq_toLp_eq_integral]
  exact hi

end OAI.Analysis.PDE.Weak
