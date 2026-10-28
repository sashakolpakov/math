import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorProjectionNorm
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature

/-! # One Covector Anti Projection -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection

noncomputable section

section

/-! Constant antiholomorphic projection on a chart fiber commutes with the actual complex-compatible line connection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def oneCovectorAntiProjection : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  AntiOneFormCoordinates.oneFormLinearEquiv.toContinuousLinearMap.comp
    (((Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ).restrictScalars ℝ).comp AntiOneFormCoordinates.oneFormLinearEquiv.symm.toContinuousLinearMap)

theorem oneCovectorAntiProjection_apply (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin 1 → E) :
    oneCovectorAntiProjection a v =
      (1 / 2 : ℂ) * (a v + Complex.I * a (fun _ => Complex.I • v 0)) := by
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (AntiOneFormCoordinates.oneFormLinear a) (v 0) = _
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, ← AntiOneFormCoordinates.oneFormLinear_reconstruct]
  rfl

theorem oneCovectorAntiProjection_eq_of_anti (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (ha : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 a) :
    oneCovectorAntiProjection a = a := by
  change AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (AntiOneFormCoordinates.oneFormLinear a)) = a
  rw [AntiOneFormCoordinates.oneFormLinear_antilinearPart ha]
  exact AntiOneFormCoordinates.oneFormLinearEquiv.apply_symm_apply a

theorem oneCovectorAntiProjection_anti (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 0 1 (oneCovectorAntiProjection a) := by
  intro z v
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (AntiOneFormCoordinates.oneFormLinear a) ((z : ℂ) • v 0) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 0 1 z * Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (AntiOneFormCoordinates.oneFormLinear a) (v 0)
  simpa only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, pow_zero, one_mul, smul_eq_mul] using
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E ℂ (AntiOneFormCoordinates.oneFormLinear a) (z : ℂ) (v 0)

theorem oneCovectorAntiProjection_idempotent (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    oneCovectorAntiProjection (oneCovectorAntiProjection a) = oneCovectorAntiProjection a :=
  oneCovectorAntiProjection_eq_of_anti _ (oneCovectorAntiProjection_anti a)

theorem oneCovectorAntiProjection_norm_le (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    ‖oneCovectorAntiProjection a‖ ≤ ‖a‖ := by
  change ‖AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (AntiOneFormCoordinates.oneFormLinear a))‖ ≤ ‖a‖
  rw [OneCovectorProjectionNorm.oneFormLinearEquiv_norm]
  exact (OneCovectorProjectionNorm.complexAntilinearPart_covector_norm_le (AntiOneFormCoordinates.oneFormLinear a)).trans_eq (OneCovectorProjectionNorm.oneFormLinear_norm a)

theorem oneCovectorAntiProjection_connection_operator
    (G : E →L[ℝ] E →L[ℝ] E) (A : E →L[ℝ] ℂ)
    (hG : ∀ v w, G v (Complex.I • w) = Complex.I • G v w)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : E) :
    Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 G A v (oneCovectorAntiProjection a) =
      oneCovectorAntiProjection (Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 G A v a) := by
  ext t
  simp only [Line.CovectorConnectionOperator.lineCovectorConnectionOperator_apply, ContinuousAlternatingMap.add_apply,
    ContinuousAlternatingMap.neg_apply, ContinuousAlternatingMap.smul_apply,
    OneCovectorCurvature.covectorInfinitesimalAction_one_apply, oneCovectorAntiProjection_apply, smul_eq_mul, hG]
  ring

theorem oneCovectorAntiProjection_covariant_derivative
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) {x : E} (ha : DifferentiableAt ℝ a x)
    (hG : ∀ v w, G x v (Complex.I • w) = Complex.I • G x v w) (v : E) :
    Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A (fun y => oneCovectorAntiProjection (a y)) x v =
      oneCovectorAntiProjection (Line.ConnectionSymbols.lineCovectorConnectionDerivative 1 G A a x v) := by
  have hd := congrArg (fun L : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 => L v)
    ((oneCovectorAntiProjection (E := E)).hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  rw [Line.CovectorConnectionOperator.lineCovectorConnectionDerivative_operator, Line.CovectorConnectionOperator.lineCovectorConnectionDerivative_operator,
    OperatorConnectionCurvature.operatorConnectionDerivative, OperatorConnectionCurvature.operatorConnectionDerivative, map_add,
    oneCovectorAntiProjection_connection_operator (G x) (A x) hG]
  exact congrArg (fun t : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 => t + oneCovectorAntiProjection
    (Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G x) (A x) v (a x))) hd

end

/-! Antiholomorphic one-covector projection commutes with an actual complex-linear change of chart coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem oneCovectorAntiProjection_comp (L : E →L[ℂ] F) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue F 1) :
    oneCovectorAntiProjection (a.compContinuousLinearMap (L.restrictScalars ℝ)) =
      (oneCovectorAntiProjection a).compContinuousLinearMap (L.restrictScalars ℝ) := by
  ext v
  simp only [oneCovectorAntiProjection_apply, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  change (1 / 2 : ℂ) * (a (fun i => L (v i)) + Complex.I * a (fun _ => L (Complex.I • v 0))) =
    (1 / 2 : ℂ) * (a (fun i => L (v i)) + Complex.I * a (fun _ => Complex.I • L (v 0)))
  simp only [map_smul]

theorem oneCovectorAntiProjection_formula (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    oneCovectorAntiProjection a = (1 / 2 : ℂ) • (a + Complex.I •
      a.compContinuousLinearMap (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
  ext v
  rw [oneCovectorAntiProjection_apply]
  change (1 / 2 : ℂ) * (a v + Complex.I * a (fun _ => Complex.I • v 0)) =
    (1 / 2 : ℂ) * (a v + Complex.I * a (fun j => Complex.I • v j))
  congr 3
  apply congrArg a
  funext j
  exact congrArg (fun k : Fin 1 => Complex.I • v k) (Subsingleton.elim 0 j)

theorem oneCovectorAntiProjection_complex_smul (c : ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    oneCovectorAntiProjection (c • a) = c • oneCovectorAntiProjection a := by
  ext v
  simp only [oneCovectorAntiProjection_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorAntiProjection
