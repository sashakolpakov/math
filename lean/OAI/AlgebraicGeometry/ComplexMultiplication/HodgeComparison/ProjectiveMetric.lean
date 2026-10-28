import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion
import OAI.Analysis.DifferentialForms.Manifold.SquareZeroD
import OAI.Analysis.DifferentialForms.Manifold.NormedSpace
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import OAI.Analysis.DifferentialForms.Manifold.Bidegree

/-! # Projective Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveMetric.CM.Construction

noncomputable section

/-! The genuine smooth Fubini--Study curvature on an affine projective chart.
The pointwise Hermitian and curvature calculations reuse the checked RiemannProjectivity proof. -/

open scoped ContDiff

variable {ι : Type*} [Fintype ι]

def affineProjectiveLift (z : ι → ℂ) : Option ι → ℂ
  | none => 1
  | some i => z i

def affineProjectiveDifferential : (ι → ℂ) →L[ℂ] (Option ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => match i with
    | none => 0
    | some j => ContinuousLinearMap.proj j)

omit [Fintype ι] in
theorem affineProjectiveLift_ne_zero (z : ι → ℂ) : affineProjectiveLift z ≠ 0 := by
  intro h
  have h0 := congrFun h none
  exact one_ne_zero h0

omit [Fintype ι] in
theorem affineProjectiveDifferential_injective :
    Function.Injective (affineProjectiveDifferential (ι := ι)) := by
  intro u v h
  funext i
  exact congrFun h (some i)

theorem affineProjectiveLift_hasFDerivAt (z : ι → ℂ) :
    HasFDerivAt affineProjectiveLift affineProjectiveDifferential z := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases i with
  | none => exact hasFDerivAt_const _ _
  | some i => exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).hasFDerivAt

theorem affineProjectiveLift_contDiff : ContDiff ℂ ∞ (affineProjectiveLift (ι := ι)) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | none => exact contDiff_const
  | some i =>
    change ContDiff ℂ ∞ (fun z : ι → ℂ => z i)
    exact (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).contDiff

@[simp]
theorem affineProjectiveLift_fderiv (z : ι → ℂ) :
    fderiv ℂ affineProjectiveLift z = affineProjectiveDifferential :=
  (affineProjectiveLift_hasFDerivAt z).fderiv

theorem affineProjectiveLift_coordinateNormSq (z : ι → ℂ) :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq (affineProjectiveLift z) = 1 + ∑ i, Complex.normSq (z i) := by
  simp [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq, Fintype.sum_option, affineProjectiveLift]

def realCoordinateCovector (i : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (Complex.reCLM.comp
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ))

def imagCoordinateCovector (i : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (Complex.imCLM.comp
    ((ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ).restrictScalars ℝ))

/-- The actual Berry connection covector in the normalized affine lift (1,z). -/
def affineBerryCovector (z : ι → ℂ) : (ι → ℂ) →L[ℝ] ℂ :=
  (1 / (2 * Real.pi * (1 + ∑ i, Complex.normSq (z i))) : ℝ) •
    ∑ i, ((z i).re • imagCoordinateCovector i - (z i).im • realCoordinateCovector i)

theorem affineBerryCovector_smooth : ContDiff ℝ ∞ (affineBerryCovector (ι := ι)) := by
  have hre (i : ι) : ContDiff ℝ ∞ (fun z : ι → ℂ => (z i).re) :=
    Complex.reCLM.contDiff.comp (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).contDiff
  have him (i : ι) : ContDiff ℝ ∞ (fun z : ι → ℂ => (z i).im) :=
    Complex.imCLM.contDiff.comp (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).contDiff
  have hn : ∀ z : ι → ℂ, 2 * Real.pi * (1 + ∑ i, Complex.normSq (z i)) ≠ 0 := by
    intro z
    have hs : 0 ≤ ∑ i, Complex.normSq (z i) := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (z i))
    positivity
  unfold affineBerryCovector
  refine ContDiff.smul (f := fun z : ι → ℂ => 1 / (2 * Real.pi * (1 + ∑ i, Complex.normSq (z i))))
    (g := fun z : ι → ℂ => ∑ i, ((z i).re • imagCoordinateCovector i -
      (z i).im • realCoordinateCovector i)) ?_ ?_
  · apply contDiff_const.div
    · simp only [Complex.normSq_apply]
      fun_prop
    · exact hn
  · fun_prop

theorem affineBerryCovector_apply (z u : ι → ℂ) :
    affineBerryCovector z u = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (affineProjectiveLift z) affineProjectiveDifferential.toLinearMap u) := by
  rw [affineBerryCovector, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection, affineProjectiveLift_coordinateNormSq]
  simp only [smul_apply, sum_apply, sub_apply, imagCoordinateCovector, realCoordinateCovector,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.imCLM_apply, Complex.reCLM_apply,
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinatePairing, Fintype.sum_option, affineProjectiveLift, affineProjectiveDifferential,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_coe, zero_apply,
    mul_zero, zero_add, Complex.im_sum, Complex.mul_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Complex.real_smul]
  push_cast
  simp only [neg_mul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
  ring

def affineBerryOneForm : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (ι → ℂ) 1 :=
  OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.ofSmooth
    (fun z => ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ (0 : Fin 1)
      (affineBerryCovector z))
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ι → ℂ) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp affineBerryCovector_smooth)

theorem affineBerryOneForm_apply (z : ι → ℂ) (v : Fin 1 → (ι → ℂ)) :
    affineBerryOneForm z v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (affineProjectiveLift z)
        affineProjectiveDifferential.toLinearMap (v 0)) := by
  exact affineBerryCovector_apply z (v 0)

theorem affineBerryCovector_directional (z u v : ι → ℂ) :
    fderiv ℝ (fun y => affineBerryCovector y v) z u = Complex.ofReal
      (deriv (fun t : ℝ => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (affineProjectiveLift (z + t • u))
        affineProjectiveDifferential.toLinearMap v) 0) := by
  have hf : ContDiffAt ℂ 2 affineProjectiveLift z :=
    affineProjectiveLift_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hb := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection_hasDerivAt_line hf (affineProjectiveLift_ne_zero z) u v
  simp only [affineProjectiveLift_fderiv] at hb
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hb
  have hd : DifferentiableAt ℝ (fun y => affineBerryCovector y v) z :=
    ((ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp
      affineBerryCovector_smooth).contDiffAt.differentiableAt (by simp)
  rw [hb.deriv]
  apply (hd.hasFDerivAt.hasLineDerivAt u).unique
  simpa only [HasLineDerivAt, Function.comp_def, affineBerryCovector_apply,
    Complex.ofRealCLM_apply] using hr

/-- Fubini--Study curvature, defined using the actual exterior derivative. -/
def affineFubiniStudyTwoForm : OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm (ι → ℂ) 2 := OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d affineBerryOneForm

theorem affineFubiniStudyTwoForm_closed :
    OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d (affineFubiniStudyTwoForm (ι := ι)) = 0 :=
  OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_d affineBerryOneForm

theorem affineFubiniStudyTwoForm_apply (z : ι → ℂ) (v : Fin 2 → (ι → ℂ)) :
    affineFubiniStudyTwoForm z v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm (affineProjectiveLift z)
        affineProjectiveDifferential.toLinearMap (v 0) (v 1)).im := by
  have hf : ContDiffAt ℂ 2 affineProjectiveLift z :=
    affineProjectiveLift_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hc := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection_curvature hf (affineProjectiveLift_ne_zero z) (v 0) (v 1)
  simp only [affineProjectiveLift_fderiv] at hc
  rw [affineFubiniStudyTwoForm, OAI.Analysis.DifferentialForms.Manifold.Basic.SmoothForm.d_apply_vectors, Fin.sum_univ_two]
  change (1 : ℤ) • fderiv ℝ (fun y => affineBerryCovector y (v 1)) z (v 0) +
    (-1 : ℤ) • fderiv ℝ (fun y => affineBerryCovector y (v 0)) z (v 1) = _
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg, affineBerryCovector_directional]
  rw [← Complex.ofReal_sub, hc]

theorem affineFubiniStudyHermitian_positive (z u : ι → ℂ) (hu : u ≠ 0) :
    0 < (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm (affineProjectiveLift z)
      affineProjectiveDifferential.toLinearMap u u).re := by
  exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_positive _ _ affineProjectiveDifferential_injective
    none one_ne_zero (fun _ => rfl) u hu

theorem affineFubiniStudyTwoForm_positive (z u : ι → ℂ) (hu : u ≠ 0) :
    0 < (affineFubiniStudyTwoForm z ![u, Complex.I • u]).re := by
  rw [affineFubiniStudyTwoForm_apply]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_smul,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.ofReal_re] using affineFubiniStudyHermitian_positive z u hu

theorem affineFubiniStudyTwoForm_hasBidegree (z : ι → ℂ) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ι → ℂ) 1 1 (affineFubiniStudyTwoForm z) := by
  intro c v
  change affineFubiniStudyTwoForm z (fun i : Fin 2 => (c : ℂ) • v i) =
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 c * affineFubiniStudyTwoForm z v
  rw [affineFubiniStudyTwoForm_apply, affineFubiniStudyTwoForm_apply]
  simp only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one,
    map_smulₛₗ, starRingEnd_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  simp only [← mul_assoc, Complex.star_def, Complex.mul_conj,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.ofReal_mul]

/-- The genuine smooth positive closed form on the normalized affine chart has type (1,1). -/
def affineFubiniStudyPureForm : OAI.Analysis.DifferentialForms.Manifold.Bidegree.PureSmoothForm (ι → ℂ) 1 1 :=
  ⟨affineFubiniStudyTwoForm,
    (OAI.Analysis.DifferentialForms.Manifold.Bidegree.mem_pureSmoothFormSubmodule _ _ _ _).mpr affineFubiniStudyTwoForm_hasBidegree⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveMetric.CM.Construction
