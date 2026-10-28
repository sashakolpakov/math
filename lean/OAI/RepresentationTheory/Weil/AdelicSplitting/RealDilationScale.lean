import OAI.RepresentationTheory.Weil.AdelicSplitting.CorrectedGeneratorKernels
import OAI.RepresentationTheory.Weil.AdelicSplitting.DeterminantMeasure

/-! # Real Dilation Scale -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.RealDilationScale

noncomputable section

/-! The actual real Haar modulus and the open-cell normalization factor
for every one-dimensional dilation with no fixed vectors. -/

open _root_.MeasureTheory
open scoped Pointwise

namespace LocalAnalysis

theorem localModulus_real (a : ℝˣ) : Local.FunctionsMetaplectic.Construction.localModulus ℝ a = |(a : ℝ)| := by
  have h := distribHaarChar_mul (volume : Measure ℝ) a (Set.Ioc (0 : ℝ) 1)
  have hs : a • Set.Ioc (0 : ℝ) 1 = (a : ℝ) • Set.Ioc (0 : ℝ) 1 := rfl
  rw [hs, Measure.addHaar_smul, Module.finrank_self, pow_one, Real.volume_Ioc,
    sub_zero, ENNReal.ofReal_one, mul_one, mul_one] at h
  have ht := congrArg ENNReal.toReal h
  simpa only [Local.FunctionsMetaplectic.Construction.localModulus, ENNReal.coe_toReal, ENNReal.toReal_ofReal (abs_nonneg _)] using ht

end LocalAnalysis

namespace Construction
open OAI.RepresentationTheory.Weil.AdelicSplitting.RealDilationScale.LocalAnalysis

theorem oneCoordinateDilation_difference_det (a : ℝ) (ha : a ≠ 0) :
    ((Local.Generators.Construction.leviSymplectic (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha)).val - 1).det = -(a - 1) ^ 2 / a := by
  have he : (Local.Generators.Construction.leviSymplectic (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha)).val - 1 =
      Matrix.fromBlocks (fun _ _ => a - 1 : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (fun _ _ => a⁻¹ - 1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    apply Matrix.ext
    intro i j
    cases i <;> cases j <;> rename_i i j <;> fin_cases i <;> fin_cases j
    · rfl
    · change (0 : ℝ) - (if Sum.inl (0 : Fin 1) = Sum.inr (0 : Fin 1) then 1 else 0) = 0
      simp
    · change (0 : ℝ) - (if Sum.inr (0 : Fin 1) = Sum.inl (0 : Fin 1) then 1 else 0) = 0
      simp
    · rfl
  rw [he]
  erw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_one, Matrix.det_fin_one]
  field_simp
  ring

theorem oneCoordinateDilation_scale (a : ℝ) (ha : a ≠ 0) (ha1 : a ≠ 1) :
    Normalization.Construction.openCellScale ℝ 1 (Local.Generators.Construction.leviSymplectic (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha)) =
      |a - 1| / Real.sqrt |a| := by
  have hn : ((Local.Generators.Construction.leviSymplectic (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha)).val - 1).det ≠ 0 := by
    rw [oneCoordinateDilation_difference_det]
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ (sub_ne_zero.mpr ha1))) ha
  rw [Normalization.Construction.openCellScale, dite_eq_left hn, LocalAnalysis.localModulus_real, Units.val_mk0,
    oneCoordinateDilation_difference_det, abs_div, abs_neg, abs_pow,
    Real.sqrt_div (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]

theorem oneCoordinateDilation_levi_coefficient (a : ℝ) (ha : a ≠ 0) :
    (Real.sqrt (Local.FunctionsMetaplectic.Construction.localModulus ℝ (Local.FunctionsMetaplectic.Construction.determinantUnit ℝ (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha))))⁻¹ =
      (Real.sqrt |a|)⁻¹ := by
  rw [LocalAnalysis.localModulus_real]
  congr 3
  change (CorrectedGeneratorKernels.Construction.oneCoordinateDilation ℝ a ha).val.det = a
  rw [Matrix.det_fin_one]
  rfl

end Construction

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.RealDilationScale
