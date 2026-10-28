import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication

/-! # Smooth Scalar Construction -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction

noncomputable section

/-! An actual smooth complex-valued function determines its ordinary smooth
zero-form, with no choice of representatives or cohomology classes. -/

open Set
open scoped _root_.Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

theorem scalarManifoldForm_smooth (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) :
    Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar (E := E) f) univ := by
  intro e he
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar_inChart]
  have heSmooth : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm e.target :=
    contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)
  have hchart : ContDiffOn ℝ ∞ (f ∘ e.symm) (Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e univ) :=
    ((hf.contMDiffOn (s := univ)).comp (heSmooth.mono inter_subset_left) (fun _ hy => hy.2)).contDiffOn
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn hchart

def scalarManifoldForm (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
  Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ofSmooth (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.ofScalar f) (scalarManifoldForm_smooth f hf)

theorem scalarManifoldForm_apply (f : M → ℂ)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ f) (x : M)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) : scalarManifoldForm f hf x v = f x := rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction.CM.Construction
