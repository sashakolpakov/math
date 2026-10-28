import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BerryGauge
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothScalarConstruction
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive

/-! # Logarithmic Phase -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LogarithmicPhase.CM.Construction

noncomputable section

/-! A holomorphic logarithm supplies the actual scalar primitive of
the change in the normalized projective connection. -/

open scoped _root_.Manifold ContDiff

def normalizedImaginaryPart : ℂ →L[ℝ] ℂ :=
  (1 / (2 * Real.pi) : ℝ) • (Complex.ofRealCLM.comp Complex.imCLM)

theorem normalizedImaginaryPart_apply (z : ℂ) :
    normalizedImaginaryPart z = (z.im / (2 * Real.pi) : ℝ) := by
  change (1 / (2 * Real.pi) : ℝ) • (z.im : ℂ) = _
  rw [Complex.real_smul, ← Complex.ofReal_mul]
  congr 1
  ring

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def logarithmicPhasePrimitive (l : M → ℂ)
    (hl : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ l) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 :=
  SmoothScalarConstruction.CM.Construction.scalarManifoldForm (normalizedImaginaryPart ∘ l)
    (normalizedImaginaryPart.contDiff.comp_contMDiff (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hl))

theorem logarithmicPhasePrimitive_d_inChart (l : M → ℂ)
    (hl : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ l)
    (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    {z : E} (hz : z ∈ e.target) (v : Fin 1 → E) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (logarithmicPhasePrimitive l hl)).val.inChart e z v =
      normalizedImaginaryPart (fderiv ℂ (l ∘ e.symm) z (v 0)) := by
  rw [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_inChart _ e he hz, HolomorphicPrimitive.CM.Construction.zeroFormScalar_reconstruct,
    extDeriv_constOfIsEmpty]
  change fderiv ℝ (normalizedImaginaryPart ∘ l ∘ e.symm) z (v 0) = _
  have hc : ContDiffAt ℂ ∞ (l ∘ e.symm) z :=
    ((hl (e.symm z)).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hz)).contDiffAt
  have hd := (hc.restrict_scalars ℝ).differentiableAt (by simp)
  have hchain := (normalizedImaginaryPart.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  rw [hchain, (hc.differentiableAt (by simp)).fderiv_restrictScalars ℝ]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LogarithmicPhase.CM.Construction
