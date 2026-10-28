import OAI.AlgebraicGeometry.DivisorClass.Chern.OperatorConnectionCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.OneCovectorCurvature
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.CurvatureContraction

/-! # Base Curvature Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureAction

noncomputable section

/-! The base-curvature term in the Bochner formula as an actual projected one-covector. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

local instance baseAction_endNormed : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance baseAction_endSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance baseAction_directionNormed : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance baseAction_directionSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

def baseCurvatureContraction (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : E →L[ℝ] ℂ :=
  -∑ i, (AntiOneFormCoordinates.oneFormLinear a).comp
    ((ContinuousLinearMap.apply ℝ E (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)).comp
      (OperatorConnectionCurvature.operatorConnectionCurvatureRight G x (b i)))

theorem baseCurvatureContraction_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (w : E) :
    baseCurvatureContraction b B G x a w =
      -∑ i, (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w) a)
        (fun _ => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) := by
  simp only [baseCurvatureContraction, neg_apply, sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, OperatorConnectionCurvature.operatorConnectionCurvatureRight_apply,
    OneCovectorCurvature.covectorInfinitesimalAction_one_apply, AntiOneFormCoordinates.oneFormLinear_apply]

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def baseCurvatureAction (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  AntiOneFormCoordinates.oneFormLinearEquiv (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (baseCurvatureContraction b B G x a))

theorem baseCurvatureAction_apply (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (x : E) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (w : E) :
    baseCurvatureAction b B G x a (fun _ => w) =
      (1 / 2 : ℂ) * ∑ i,
        (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) w) a)
            (fun _ => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) +
          Complex.I * (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (OperatorConnectionCurvature.operatorConnectionCurvature G x (b i) (Complex.I • w)) a)
            (fun _ => Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap))) := by
  change Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E ℂ (baseCurvatureContraction b B G x a) w = _
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply]
  simp only [baseCurvatureContraction_apply, smul_eq_mul, Finset.sum_neg_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.BaseCurvatureAction
