import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence

/-! # Covector Forms -/

namespace OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorForms

noncomputable section

/-! A holomorphic complex covector field on an open vector domain is
an actual smooth real one-form, with the same evaluations. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]

def complexCovectorRealLinear : (E →L[ℂ] ℂ) →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E 1 :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ) (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.restrictScalarsL ℂ E ℂ ℝ ℝ)

omit [FiniteDimensional ℂ E] in
theorem complexCovectorRealLinear_apply (a : E →L[ℂ] ℂ) :
    complexCovectorRealLinear a = Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E a := rfl

def holomorphicCovectorOpenForm (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 1 := by
  refine ⟨fun x => Analysis.DifferentialForms.Manifold.Bidegree.complexLinearCovector E (a x.val), ?_⟩
  have h := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn U.isOpen ha
  have hc := complexCovectorRealLinear.contDiff.comp_contDiffOn (h.restrict_scalars ℝ)
  apply hc.congr
  intro x hx
  exact Analysis.DifferentialForms.Manifold.OpenD.openFormExtension_apply U _ ⟨x, hx⟩

theorem holomorphicCovectorOpenForm_apply (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) (x : U) (v : Fin 1 → E) :
    holomorphicCovectorOpenForm U a ha x v = a x.val (v 0) := rfl

def holomorphicCovectorManifoldForm (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 1 :=
  Analysis.DifferentialForms.Manifold.OpenEquivalence.smoothOpenManifoldEquiv U 1 (holomorphicCovectorOpenForm U a ha)

omit [FiniteDimensional ℂ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem openTangentEquiv_apply_id (U : Opens E) (x : U) (v : E) : Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x v = v := by
  have h := mfderiv_extChartAt_self (I := 𝓘(ℝ, E)) (x := x)
  exact congrArg (fun b : E →L[ℝ] E => b v) h

theorem holomorphicCovectorManifoldForm_apply (U : Opens E) (a : E → E →L[ℂ] ℂ)
    (ha : DifferentiableOn ℂ a U) (x : U) (v : Fin 1 → E) :
    holomorphicCovectorManifoldForm U a ha x v = a x.val (v 0) := by
  change a x.val (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv x (v 0)) = _
  rw [openTangentEquiv_apply_id]

end

end OAI.RepresentationTheory.Theta.Geometric.Complex.CovectorForms
