import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.ChartCoefficients
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.HolomorphicPullback
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

/-! # Function Multiplication -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionMultiplication

noncomputable section

/-! Actual holomorphic functions multiply actual holomorphic forms on every complex manifold. -/

open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

def multiplyByHolomorphicFunction (f : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯) (n : ℕ) :
    DeRhamComplex.forms E M n →ₗ[ℂ] DeRhamComplex.forms E M n where
  toFun a := by
    let s := Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex f.property)
      (DeRhamComplex.inclusion E M n a)
    have hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 s.val := by
      intro e he y hy
      change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f (DeRhamComplex.inclusion E M n a).val).inChart e y)
      rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
      exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).smul_mem _ (a.val.hasBidegree_inChart e he hy)
    let p : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M n 0 := ⟨s, hp⟩
    have hh : p ∈ DeRhamComplex.forms E M n := by
      apply (ChartCoefficients.mem_forms_iff_coefficients_complex p).mpr
      intro e he y hy
      change DifferentiableAt ℂ ((Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.smulFunction f (DeRhamComplex.inclusion E M n a).val).inChart e) y
      rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smulFunction]
      have hi : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ e.symm y :=
        contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hy
      have hf : DifferentiableAt ℂ (fun z => f (e.symm z)) y :=
        ((f.property _).comp y hi).contDiffAt.differentiableAt (by simp)
      exact hf.smul (ChartCoefficients.form_coefficients_complex a e he hy)
    exact ⟨p, hh⟩
  map_add' a b := by
    apply HolomorphicPullback.inclusion_injective n
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex f.property)).map_add
      (DeRhamComplex.inclusion E M n a) (DeRhamComplex.inclusion E M n b)
  map_smul' c a := by
    apply HolomorphicPullback.inclusion_injective n
    exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction f (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex f.property)).map_smul c
      (DeRhamComplex.inclusion E M n a)

theorem multiplyByHolomorphicFunction_apply (f : C^∞⟮𝓘(ℂ, E), M; 𝓘(ℂ), ℂ⟯)
    (n : ℕ) (a : DeRhamComplex.forms E M n) (x : M) :
    DeRhamComplex.inclusion E M n (multiplyByHolomorphicFunction f n a) x = f x • DeRhamComplex.inclusion E M n a x := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FunctionMultiplication
