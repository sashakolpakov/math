import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CovectorConnectionOperator

/-! # One Covector Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature

noncomputable section

/-! On genuine one-covectors, line curvature separates exactly from base curvature. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.CovectorConnectionOperator.lineOperator_formNormed Line.CovectorConnectionOperator.lineOperator_formSpace
  Line.CovectorConnectionOperator.lineOperator_endNormed Line.CovectorConnectionOperator.lineOperator_endSpace Line.CovectorConnectionOperator.lineOperator_directionNormed Line.CovectorConnectionOperator.lineOperator_directionSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorInfinitesimalAction_complex_smul (n : ℕ)
    (G : E →L[ℝ] E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (c : ℂ) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G (c • a) = c • Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction n G a := by
  ext v
  simp only [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction_apply, ContinuousAlternatingMap.smul_apply,
    Finset.smul_sum]

theorem covectorInfinitesimalAction_one_apply (G : E →L[ℝ] E)
    (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (v : Fin 1 → E) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 G a v = a (fun _ => G (v 0)) := by
  rw [Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction_apply, Fin.sum_univ_one]
  congr 1
  funext j
  fin_cases j
  rfl

theorem covectorInfinitesimalAction_one_comp (G H : E →L[ℝ] E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 G (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 H a) =
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (H.comp G) a := by
  ext v
  simp only [covectorInfinitesimalAction_one_apply, ContinuousLinearMap.comp_apply]

theorem lineCovectorConnectionCurvature_one
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) {x : E}
    (hG : DifferentiableAt ℝ G x) (hA : DifferentiableAt ℝ A x)
    (v w : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) :
    OperatorConnectionCurvature.operatorConnectionCurvature (fun y => Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G y) (A y)) x v w a =
      -Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x v w) a +
        (fderiv ℝ A x v w - fderiv ℝ A x w v) • a := by
  change fderiv ℝ (fun y => Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G y) (A y)) x v w a -
      fderiv ℝ (fun y => Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G y) (A y)) x w v a +
      Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G x) (A x) v (Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G x) (A x) w a) -
      Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G x) (A x) w (Line.CovectorConnectionOperator.lineCovectorConnectionOperator 1 (G x) (A x) v a) = _
  rw [Line.CovectorConnectionOperator.lineCovectorConnectionOperator_derivative 1 G A hG hA,
    Line.CovectorConnectionOperator.lineCovectorConnectionOperator_derivative 1 G A hG hA]
  simp only [Line.CovectorConnectionOperator.lineCovectorConnectionOperator_apply, map_add, map_neg,
    covectorInfinitesimalAction_complex_smul, covectorInfinitesimalAction_one_comp,
    neg_add_rev, neg_neg, sub_smul]
  have hbase : Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x v w) a =
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (fderiv ℝ G x v w) a -
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (fderiv ℝ G x w v) a +
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 ((G x v).comp (G x w)) a -
      Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 ((G x w).comp (G x v)) a := by
    change Line.CovectorConnectionOperator.covectorActionOperator 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x v w) a = _
    simp only [OperatorConnectionCurvature.operatorConnectionCurvature, map_sub, map_add, _root_.sub_apply, _root_.add_apply,
      Line.CovectorConnectionOperator.covectorActionOperator_apply]
  rw [hbase, smul_comm (A x v) (A x w) a]
  abel

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature
