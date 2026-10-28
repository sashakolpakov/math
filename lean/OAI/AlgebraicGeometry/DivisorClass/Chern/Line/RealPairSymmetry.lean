import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughDivergence
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe

/-! # Real Pair Symmetry -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RealPairSymmetry

noncomputable section

/-! Real symmetry of the exact weighted line metric and full covariant energy pairings. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem complex_real_weight_pair_re (r : ℝ) (w z : ℂ) (hw : w = Complex.ofReal w.re) :
    ((r : ℂ) * w * z).re = r * w.re * z.re := by
  rw [hw]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero]

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineMetricTestPair_re_symm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hB : ∀ v t, B x v t = B x t v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hw : w x = Complex.ofReal (w x).re) :
    (TensorMetricTest.lineMetricTestPair b n B w a c x).re = (TensorMetricTest.lineMetricTestPair b n B w c a x).re := by
  unfold TensorMetricTest.lineMetricTestPair
  rw [complex_real_weight_pair_re _ _ _ hw, complex_real_weight_pair_re _ _ _ hw]
  apply congrArg (fun r : ℝ => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) * (w x).re * r)
  have hs := congrArg Complex.re (Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_symm b n (B x) hB hpos (a x) (c x))
  simpa only [Complex.star_def, Complex.conj_re] using hs.symm

theorem lineCovectorFullEnergyPair_re_symm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ)
    (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hB : ∀ v t, B x v t = B x t v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hw : w x = Complex.ofReal (w x).re) :
    (RoughDivergence.lineCovectorFullEnergyPair b n B G A w a c x).re =
      (RoughDivergence.lineCovectorFullEnergyPair b n B G A w c a x).re := by
  unfold RoughDivergence.lineCovectorFullEnergyPair
  rw [complex_real_weight_pair_re _ _ _ hw, complex_real_weight_pair_re _ _ _ hw]
  exact congrArg (fun r : ℝ => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) * (w x).re * r)
    (TensorMetricRe.covectorTensorMetricPair_re_symm b n (B x) hB hpos _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RealPairSymmetry
