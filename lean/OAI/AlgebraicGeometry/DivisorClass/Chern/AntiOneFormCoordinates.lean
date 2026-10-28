import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.DolbeaultPrime

/-! # Anti One Form Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates

noncomputable section

section

/-! Actual one-form coefficients and the conjugate-linearity of type `(0,1)`. -/

open _root_.ContinuousAlternatingMap _root_.TopologicalSpace
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def oneFormLinearEquiv : (E →L[ℝ] ℂ) ≃L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv

def oneFormLinear (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : E →L[ℝ] ℂ := oneFormLinearEquiv.symm a

theorem oneFormLinear_apply (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : E) :
    oneFormLinear a v = a (fun _ => v) := rfl

theorem oneFormLinear_reconstruct (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin 1 → E) :
    a v = oneFormLinear a (v 0) := by
  rw [oneFormLinear_apply]
  congr 1
  funext i
  congr 1
  exact Subsingleton.elim _ _

theorem openOneForm_coefficient_smooth {U : Opens E} (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1) (v : E) :
    ContDiffOn ℝ ∞ (fun x => oneFormLinear (a.extension x) v) (U : Set E) :=
  (a.smooth.continuousLinearMap_comp oneFormLinearEquiv.symm.toContinuousLinearMap).clm_apply
    contDiffOn_const

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [IsScalarTower ℝ ℂ E] in
theorem oneFormLinear_complex_smul {a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1} (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a)
    (c : ℂ) (v : E) : oneFormLinear a (c • v) = star c * oneFormLinear a v := by
  by_cases hc : c = 0
  · subst c
    simp
  · have h := ha (Units.mk0 c hc) (fun _ => v)
    simpa only [Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree, Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, pow_one, one_mul,
      Units.val_mk0, oneFormLinear_apply] using h

theorem oneFormLinear_antilinearPart {a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1} (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (oneFormLinear a) = oneFormLinear a := by
  ext v
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, oneFormLinear_complex_smul ha]
  simp only [Complex.star_def, Complex.conj_I, smul_eq_mul, neg_mul]
  ring_nf
  simp
  ring

end

/-! The original Dolbeault differential of one-forms is the antisymmetrized scalar derivative. -/

open _root_.ContinuousAlternatingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def oneFormCoefficientCLM (v : E) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] ℂ :=
  (ContinuousLinearMap.apply ℝ ℂ v).comp oneFormLinearEquiv.symm.toContinuousLinearMap

theorem oneFormCoefficient_fderiv {a : Analysis.DifferentialForms.Manifold.Basic.RawForm E 1} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    fderiv ℝ (fun y => oneFormLinear (a y) w) x v = oneFormLinear (fderiv ℝ a x v) w := by
  have h := ((oneFormCoefficientCLM w).hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  exact congrArg (fun D : E →L[ℝ] ℂ => D v) h

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def antilinearScalarDerivative (f : E → ℂ) (x v : E) : ℂ :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (fderiv ℝ f x) v

theorem antilinearScalarDerivative_oneFormCoefficient {a : Analysis.DifferentialForms.Manifold.Basic.RawForm E 1} {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    antilinearScalarDerivative (fun y => oneFormLinear (a y) w) x v =
      oneFormLinear (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (fderiv ℝ a x) v) w := by
  change (1 / 2 : ℂ) *
    (fderiv ℝ (fun y => oneFormLinear (a y) w) x v +
      Complex.I * fderiv ℝ (fun y => oneFormLinear (a y) w) x (Complex.I • v)) =
    (1 / 2 : ℂ) *
      (oneFormLinear (fderiv ℝ a x v) w + Complex.I * oneFormLinear (fderiv ℝ a x (Complex.I • v)) w)
  rw [oneFormCoefficient_fderiv ha, oneFormCoefficient_fderiv ha]

theorem extDerivDoublePrime_oneForm_apply (a : Analysis.DifferentialForms.Manifold.Basic.RawForm E 1) (x v w : E) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x ![v, w] =
      oneFormLinear (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (fderiv ℝ a x) v) w -
        oneFormLinear (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (fderiv ℝ a x) w) v := by
  have hlast : Fin.removeNth (1 : Fin 2) (Matrix.vecCons v (fun _ : Fin 1 => w)) = (fun _ : Fin 1 => v) := by
    funext i
    fin_cases i
    rfl
  have hsingle : ![w] = (fun _ : Fin 1 => w) := by
    funext i
    fin_cases i
    rfl
  simp [Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime, alternatizeUncurryFin_apply, Fin.sum_univ_two,
    oneFormLinear_apply, sub_eq_add_neg, hlast, hsingle]
  abel

theorem extDerivDoublePrime_oneForm_scalar (a : Analysis.DifferentialForms.Manifold.Basic.RawForm E 1) {x : E}
    (ha : DifferentiableAt ℝ a x) (v w : E) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x ![v, w] =
      antilinearScalarDerivative (fun y => oneFormLinear (a y) w) x v -
        antilinearScalarDerivative (fun y => oneFormLinear (a y) v) x w := by
  rw [extDerivDoublePrime_oneForm_apply,
    antilinearScalarDerivative_oneFormCoefficient ha,
    antilinearScalarDerivative_oneFormCoefficient ha]

theorem closed_oneForm_scalar_symmetry {a : Analysis.DifferentialForms.Manifold.Basic.RawForm E 1} {x : E}
    (ha : DifferentiableAt ℝ a x) (hclosed : Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x = 0) (v w : E) :
    antilinearScalarDerivative (fun y => oneFormLinear (a y) w) x v =
      antilinearScalarDerivative (fun y => oneFormLinear (a y) v) x w := by
  apply sub_eq_zero.mp
  rw [← extDerivDoublePrime_oneForm_scalar a ha, hclosed]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormCoordinates
