import OAI.Analysis.Calculus.Current.Fiber.Time
import OAI.Analysis.Calculus.Current.Cutoff
import OAI.Analysis.Calculus.Quaternion.CurrentIntegral

/-! The cutoff, spatially averaged, strictly positive regularized current. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder

variable {d : ℕ} {ι α : Type*} [Fintype ι] [MeasurableSpace α]

local instance : ContinuousENorm (Matrix (Index d) (Index d) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousENorm (Index d → Index d → Quaternion ℝ))

def averagedWaveCurrent (μ : Measure α) (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Matrix (Index d) (Index d) (Quaternion ℝ) :=
  ∫ t, waveCurrent κ cR cI v (x + shift t) z ∂μ

theorem averagedWaveCurrent_isHermitian (μ : Measure α) (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    (averagedWaveCurrent μ shift κ cR cI v x z).IsHermitian :=
  OAI.Analysis.Calculus.Quaternion.integral_current_isHermitian hA (Filter.Eventually.of_forall fun _ => waveCurrent_isHermitian ..)

theorem averagedWaveCurrent_nonneg (μ : Measure α) (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ)
    (ξ : Index d → Quaternion ℝ) :
    0 ≤ (star ξ ⬝ᵥ (averagedWaveCurrent μ shift κ cR cI v x z *ᵥ ξ)).re :=
  OAI.Analysis.Calculus.Quaternion.integral_current_quadratic_nonneg hA ξ
    (Filter.Eventually.of_forall fun _ => waveCurrent_quadratic_nonneg ..)

theorem averagedWaveCurrent_tangent (μ : Measure α) (shift : α → Index d → ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : Index d → ℝ) (z : Index d → ℂ)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ)
    (ξ : Index d → Quaternion ℝ) :
    (∑ b, complexK (phaseRow (ratio z) b) *
      (averagedWaveCurrent μ shift κ cR cI v x z *ᵥ ξ) b) = 0 :=
  OAI.Analysis.Calculus.Quaternion.integral_current_row_zero hA _ ξ
    (Filter.Eventually.of_forall fun _ => waveCurrent_image_tangent ..)

def timeComponent (A : Matrix (Index d) (Index d) (Quaternion ℝ)) : ℝ :=
  (A none none - A none (some none) - A (some none) none + A (some none) (some none)).re / 2

def timeVector (d : ℕ) : Index d → Quaternion ℝ :=
  Pi.single none 1 - Pi.single (some none) 1

theorem timeComponent_eq_quadratic (A : Matrix (Index d) (Index d) (Quaternion ℝ)) :
    timeComponent A = (star (timeVector d) ⬝ᵥ (A *ᵥ timeVector d)).re / 2 := by
  simp [timeComponent, timeVector, dotProduct, Matrix.mulVec, Fintype.sum_option,
    Pi.single_apply]
  ring

theorem timeComponent_nonneg (A : Matrix (Index d) (Index d) (Quaternion ℝ))
    (hA : ∀ ξ, 0 ≤ (star ξ ⬝ᵥ (A *ᵥ ξ)).re) : 0 ≤ timeComponent A := by
  rw [timeComponent_eq_quadratic]
  exact div_nonneg (hA _) (by norm_num)

theorem timeComponent_add (A B : Matrix (Index d) (Index d) (Quaternion ℝ)) :
    timeComponent (A + B) = timeComponent A + timeComponent B := by
  simp [timeComponent]
  ring

theorem timeComponent_smul (r : ℝ) (A : Matrix (Index d) (Index d) (Quaternion ℝ)) :
    timeComponent (r • A) = r * timeComponent A := by
  simp [timeComponent]
  ring

def regularizedCurrent (μ : Measure α) (shift : α → Index d → ℝ) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) : Matrix (Index d) (Index d) (Quaternion ℝ) :=
  cutoffCurrent phaseCutoff a (averagedWaveCurrent μ shift κ cR cI v) x z +
    h ^ (50 * (d + 1)) • fiberCofactor (1 / 10) a z

theorem regularizedCurrent_isHermitian (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    (regularizedCurrent μ shift h a κ cR cI v x z).IsHermitian := by
  apply Matrix.IsHermitian.add
  · exact cutoffCurrent_isHermitian _ _ _ _ _
      (averagedWaveCurrent_isHermitian μ shift κ cR cI v x z hA)
  · apply Matrix.ext
    intro i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.star_smul,
      (fiberCofactor_isHermitian (1 / 10) a z).apply]

theorem regularizedCurrent_nonneg (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hh : 0 ≤ h) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ)
    (ξ : Index d → Quaternion ℝ) :
    0 ≤ (star ξ ⬝ᵥ (regularizedCurrent μ shift h a κ cR cI v x z *ᵥ ξ)).re := by
  simp only [regularizedCurrent, Matrix.add_mulVec, dotProduct_add, Quaternion.re_add,
    Matrix.smul_mulVec, dotProduct_smul, Quaternion.re_smul, smul_eq_mul]
  exact add_nonneg
    (cutoffCurrent_quadratic_nonneg _ _ _ _ _ (phaseCutoff_nonneg _)
      (averagedWaveCurrent_nonneg μ shift κ cR cI v x z hA) ξ)
    (mul_nonneg (pow_nonneg hh _) (fiberCofactor_nonneg _ a z hY ξ))

theorem regularizedCurrent_tangent (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ)
    (ξ : Index d → Quaternion ℝ) :
    (∑ b, complexK (phaseRow (ratio z) b) *
      (regularizedCurrent μ shift h a κ cR cI v x z *ᵥ ξ) b) = 0 := by
  simp only [regularizedCurrent, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.smul_apply, mul_add, mul_smul_comm, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [cutoffCurrent_image_tangent _ _ _ _ _
    (averagedWaveCurrent_tangent μ shift κ cR cI v x z hA),
    fiberCofactor_tangent_phi _ a z ha hY ξ, smul_zero, add_zero]

theorem regularizedCurrent_time_pos (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hh : 0 < h) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hr : fiberDefining (1 / 10) a z ≤ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    0 < timeComponent (regularizedCurrent μ shift h a κ cR cI v x z) := by
  rw [regularizedCurrent, timeComponent_add, timeComponent_smul]
  apply add_pos_of_nonneg_of_pos
  · exact timeComponent_nonneg _ (cutoffCurrent_quadratic_nonneg _ _ _ _ _
      (phaseCutoff_nonneg _) (averagedWaveCurrent_nonneg μ shift κ cR cI v x z hA))
  · exact mul_pos (pow_pos hh _) (fiberTimeComponent_pos_on_fiber a z ha hY hr)

theorem regularizedCurrent_posSemidef (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (hh : 0 ≤ h) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    (OAI.LinearAlgebra.Moore.complexify (regularizedCurrent μ shift h a κ cR cI v x z)).PosSemidef :=
  (OAI.Analysis.Calculus.Quaternion.indexed_complexify_posSemidef_iff _
    (regularizedCurrent_isHermitian μ shift h a κ cR cI v x z hA)).mpr
      (regularizedCurrent_nonneg μ shift h a κ cR cI v x z hh hY hA)

theorem regularizedCurrent_background_mulVec (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ)
    (ξ : Index d → Quaternion ℝ) :
    backgroundHessian z *ᵥ (regularizedCurrent μ shift h a κ cR cI v x z *ᵥ ξ) = 0 := by
  rw [backgroundHessian_formula z hY, Matrix.smul_mulVec]
  have hzero : OAI.Analysis.Calculus.Quaternion.outer (fun b => complexK (star (phaseRow (ratio z) b))) *ᵥ
      (regularizedCurrent μ shift h a κ cR cI v x z *ᵥ ξ) = 0 := by
    funext b
    rw [OAI.Analysis.Calculus.Quaternion.outer_mulVec]
    simp only [← complexK_star, star_star,
      regularizedCurrent_tangent μ shift h a κ cR cI v x z ha hY hA ξ,
      mul_zero, Pi.zero_apply]
  rw [hzero, smul_zero]

theorem regularizedCurrent_background_mul (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    backgroundHessian z * regularizedCurrent μ shift h a κ cR cI v x z = 0 := by
  apply Matrix.ext
  intro i j
  have hh := regularizedCurrent_background_mulVec μ shift h a κ cR cI v x z ha hY hA
    (Pi.single j 1)
  rw [Matrix.mulVec_mulVec] at hh
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply, Matrix.zero_apply]
    using congrFun hh i

theorem regularizedCurrent_background_pairing (μ : Measure α) (shift : α → Index d → ℝ)
    (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : Index d → ℝ) (z : Index d → ℂ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hA : Integrable (fun t => waveCurrent κ cR cI v (x + shift t) z) μ) :
    (backgroundHessian z * regularizedCurrent μ shift h a κ cR cI v x z).trace.re = 0 := by
  rw [regularizedCurrent_background_mul μ shift h a κ cR cI v x z ha hY hA]
  simp

end OAI.Analysis.Calculus.Current
