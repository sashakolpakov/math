import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultFunctionKernel
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal
import OAI.Analysis.DifferentialForms.Manifold.DegreeZero

/-! # Dolbeault Zero Forms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroForms

noncomputable section

/-! The original degree-zero Dolbeault operator has the actual holomorphic function kernel. -/

open _root_.ContinuousAlternatingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem antilinearPart_constOfIsEmpty (D : E →L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E 0)
      ((constOfIsEmptyLIE ℝ E ℂ (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap.comp D) =
      (constOfIsEmptyLIE ℝ E ℂ (Fin 0)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ D) := by
  ext x v
  rfl

theorem extDerivDoublePrime_constOfIsEmpty (f : E → ℂ) (x : E) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => constOfIsEmpty ℝ E (Fin 0) (f y)) x =
      ofSubsingleton ℝ E ℂ (0 : Fin 1) (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (fderiv ℝ f x)) := by
  rw [Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime]
  simp only [← constOfIsEmptyLIE_apply, ← Function.comp_def _ f,
    (constOfIsEmptyLIE ℝ E ℂ (Fin 0)).comp_fderiv]
  rw [antilinearPart_constOfIsEmpty, alternatizeUncurryFin_constOfIsEmptyLIE_comp]

theorem extDerivDoublePrime_zeroForm_eq_zero_iff {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => constOfIsEmpty ℝ E (Fin 0) (f y)) x = 0 ↔
      DifferentiableAt ℂ f x := by
  rw [DolbeaultFunctionKernel.differentiableAt_complex_iff_antilinear_zero hf, extDerivDoublePrime_constOfIsEmpty]
  constructor
  · intro h
    ext v
    exact congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 => a (fun _ => v)) h
  · intro h
    rw [h]
    ext v
    rfl

theorem extDerivDoublePrime_zeroForm_eq_zero_on_open_iff
    {U : Set E} (hU : IsOpen U) {f : E → ℂ} (hf : DifferentiableOn ℝ f U) :
    (∀ x ∈ U, Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => constOfIsEmpty ℝ E (Fin 0) (f y)) x = 0) ↔
      DifferentiableOn ℂ f U := by
  constructor
  · intro h x hx
    exact ((extDerivDoublePrime_zeroForm_eq_zero_iff
      ((hf x hx).differentiableAt (hU.mem_nhds hx))).mp (h x hx)).differentiableWithinAt
  · intro h x hx
    exact (extDerivDoublePrime_zeroForm_eq_zero_iff
      ((hf x hx).differentiableAt (hU.mem_nhds hx))).mpr
      ((h x hx).differentiableAt (hU.mem_nhds hx))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultZeroForms
