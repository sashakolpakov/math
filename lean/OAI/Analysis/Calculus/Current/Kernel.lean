import OAI.Analysis.Calculus.Current.RegularizedSmooth
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! The normalized Japanese-bracket kernel used for spatial regularization. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory
open scoped ContDiff

abbrev SpatialSpace (d : ℕ) := EuclideanSpace ℝ (Option (Fin d))

def kernelProfile (d : ℕ) (x : SpatialSpace d) : ℝ :=
  (1 + ‖x‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1) + 4) / 2)

theorem kernelProfile_pos (d : ℕ) (x : SpatialSpace d) : 0 < kernelProfile d x := by
  apply Real.rpow_pos_of_pos
  positivity

theorem continuous_kernelProfile (d : ℕ) : Continuous (kernelProfile d) := by
  unfold kernelProfile
  have hc : Continuous (fun x : SpatialSpace d => (1 : ℝ) + ‖x‖ ^ 2) := by fun_prop
  exact hc.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))

theorem integrable_kernelProfile (d : ℕ) : Integrable (kernelProfile d) := by
  apply integrable_rpow_neg_one_add_norm_sq
  simp only [SpatialSpace, finrank_euclideanSpace, Fintype.card_option, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one]
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem integral_kernelProfile_pos (d : ℕ) : 0 < ∫ x, kernelProfile d x :=
  integral_pos_of_integrable_nonneg_nonzero (continuous_kernelProfile d)
    (integrable_kernelProfile d) (fun x => (kernelProfile_pos d x).le)
    (ne_of_gt (kernelProfile_pos d 0))

def kernelConstant (d : ℕ) : ℝ := (∫ x, kernelProfile d x)⁻¹

theorem kernelConstant_pos (d : ℕ) : 0 < kernelConstant d :=
  inv_pos.mpr (integral_kernelProfile_pos d)

/-- `C_n h⁻ⁿ ⟨x/h⟩⁻²ⁿ⁻⁴`, with `n=d+1`. -/
def smoothingKernel (d : ℕ) (h : ℝ) (x : SpatialSpace d) : ℝ :=
  kernelConstant d * (h ^ (d + 1))⁻¹ * kernelProfile d (h⁻¹ • x)

theorem smoothingKernel_pos (d : ℕ) (h : ℝ) (hh : 0 < h) (x : SpatialSpace d) :
    0 < smoothingKernel d h x := by
  exact mul_pos (mul_pos (kernelConstant_pos d) (inv_pos.mpr (pow_pos hh _)))
    (kernelProfile_pos d _)

theorem integrable_smoothingKernel (d : ℕ) (h : ℝ) (hh : h ≠ 0) :
    Integrable (smoothingKernel d h) :=
  ((integrable_kernelProfile d).comp_smul (inv_ne_zero hh)).const_mul _

theorem integral_smoothingKernel (d : ℕ) (h : ℝ) (hh : 0 < h) :
    ∫ x, smoothingKernel d h x = 1 := by
  simp only [smoothingKernel, integral_const_mul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (kernelProfile d) hh.le]
  simp only [SpatialSpace, finrank_euclideanSpace, Fintype.card_option, Fintype.card_fin,
    smul_eq_mul, kernelConstant]
  field_simp [ne_of_gt hh, ne_of_gt (integral_kernelProfile_pos d)]

def sourceKernelMeasure (d : ℕ) (h : ℝ) : Measure (SpatialSpace d) :=
  volume.withDensity (fun x => ENNReal.ofReal (smoothingKernel d h x))

theorem sourceKernelMeasure_isProbability (d : ℕ) (h : ℝ) (hh : 0 < h) :
    IsProbabilityMeasure (sourceKernelMeasure d h) := by
  constructor
  rw [sourceKernelMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_smoothingKernel d h hh.ne')
    (Filter.Eventually.of_forall fun x => (smoothingKernel_pos d h hh x).le)]
  rw [integral_smoothingKernel d h hh]
  simp

end OAI.Analysis.Calculus.Current
