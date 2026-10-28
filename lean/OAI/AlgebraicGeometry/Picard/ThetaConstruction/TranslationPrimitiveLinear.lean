import OAI.AlgebraicGeometry.Picard.ThetaConstruction.TranslationDolbeaultSub

/-! # Translation Primitive Linear -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! The constructed local smooth translation primitives depend
complex linearly on the actual vector parameter. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {g : ℕ} {E : DefinitionsIntegral.IntegralMatrix g} {T : DefinitionsIntegral.MarkedPolarizedTorus g E}
    (M : PeriodModel.Geometric.AlgebraicPeriodModel T)

local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationPrimitiveLinear_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance PeriodModel.Geometric.AlgebraicPeriodModel.translationPrimitiveLinear_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth

theorem PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationZeroForm_add (a b : DefinitionsIntegral.Tangent g)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    M.localTranslationZeroForm (a + b) p = M.localTranslationZeroForm a p + M.localTranslationZeroForm b p := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro q
  apply ContinuousAlternatingMap.ext
  intro v
  change (M.localTranslationZeroForm (a + b) p).val q v =
    (M.localTranslationZeroForm a p).val q v + (M.localTranslationZeroForm b p).val q v
  have h := (congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_add (T.riemannForm (M.localPeriodLift p q.val)) a b)).trans (mul_add _ _ _)
  exact (M.localTranslationZeroForm_value (a + b) p q v).trans
    (h.trans (congrArg₂ (· + ·) (M.localTranslationZeroForm_value a p q v).symm
      (M.localTranslationZeroForm_value b p q v).symm))

theorem PeriodModel.Geometric.AlgebraicPeriodModel.localTranslationZeroForm_smul (c : ℂ) (a : DefinitionsIntegral.Tangent g)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) :
    M.localTranslationZeroForm (c • a) p = c • M.localTranslationZeroForm a p := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro q
  apply ContinuousAlternatingMap.ext
  intro v
  change (M.localTranslationZeroForm (c • a) p).val q v = c * (M.localTranslationZeroForm a p).val q v
  have h := congrArg (fun t : ℂ => (Real.pi : ℂ) * t)
    (map_smul (T.riemannForm (M.localPeriodLift p q.val)) c a)
  have h' : (Real.pi : ℂ) * (c • T.riemannForm (M.localPeriodLift p q.val) a) =
      c * ((Real.pi : ℂ) * T.riemannForm (M.localPeriodLift p q.val) a) := by
    change (Real.pi : ℂ) * (c * _) = _
    ring
  exact (M.localTranslationZeroForm_value (c • a) p q v).trans
    (h.trans (h'.trans (congrArg (fun t : ℂ => c * t) (M.localTranslationZeroForm_value a p q v).symm)))

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
