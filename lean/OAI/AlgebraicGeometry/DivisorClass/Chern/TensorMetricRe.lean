import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorTensorAlgebra

/-! # Tensor Metric Re -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe

noncomputable section

section

/-! Exact cancellation of line-frame transition factors in weighted covector and tensor pairings. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_weighted_gauge (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (t wi wj : ℂ)
    (hw : wi = (Complex.normSq t : ℂ) * wj) :
    wj * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (t • a) (t • c) = wi * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  rw [Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_right,
    hw, Complex.normSq_eq_conj_mul_self]
  ring

theorem covectorTensorMetricPair_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (t s : ℂ) :
    CovectorTensorAlgebra.covectorTensorMetricPair b n B (t • N) (s • P) = conj t * s * CovectorTensorAlgebra.covectorTensorMetricPair b n B N P := by
  unfold CovectorTensorAlgebra.covectorTensorMetricPair
  simp only [_root_.smul_apply, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left,
    Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem covectorTensorMetricPair_weighted_gauge (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (t wi wj : ℂ)
    (hw : wi = (Complex.normSq t : ℂ) * wj) :
    wj * CovectorTensorAlgebra.covectorTensorMetricPair b n B (t • N) (t • P) = wi * CovectorTensorAlgebra.covectorTensorMetricPair b n B N P := by
  rw [covectorTensorMetricPair_complex_smul, hw, Complex.normSq_eq_conj_mul_self]
  ring

end

section

/-! Real pairing rules and symmetry for the original positive inverse-metric tensor contraction. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem covectorTensorMetricPair_re_add_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P Q : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B (N + P) Q).re =
      (CovectorTensorAlgebra.covectorTensorMetricPair b n B N Q).re + (CovectorTensorAlgebra.covectorTensorMetricPair b n B P Q).re := by
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, _root_.add_apply, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left,
    Complex.re_sum, Complex.add_re, Finset.sum_add_distrib]

theorem covectorTensorMetricPair_re_add_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P Q : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B N (P + Q)).re =
      (CovectorTensorAlgebra.covectorTensorMetricPair b n B N P).re + (CovectorTensorAlgebra.covectorTensorMetricPair b n B N Q).re := by
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, _root_.add_apply, Line.ConnectionOperator.bilinearFormMetricPair_add_right,
    Complex.re_sum, Complex.add_re, Finset.sum_add_distrib]

theorem covectorTensorMetricPair_re_real_smul_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℝ) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B (r • N) P).re = r * (CovectorTensorAlgebra.covectorTensorMetricPair b n B N P).re := by
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, _root_.smul_apply, Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left,
    Complex.re_sum, Complex.smul_re, smul_eq_mul, Finset.mul_sum]

theorem covectorTensorMetricPair_re_real_smul_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (r : ℝ) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B N (r • P)).re = r * (CovectorTensorAlgebra.covectorTensorMetricPair b n B N P).re := by
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, _root_.smul_apply, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right,
    Complex.re_sum, Complex.smul_re, smul_eq_mul, Finset.mul_sum]

theorem covectorTensorMetricPair_re_symm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (N P : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (CovectorTensorAlgebra.covectorTensorMetricPair b n B N P).re = (CovectorTensorAlgebra.covectorTensorMetricPair b n B P N).re := by
  let F := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.RealMetricFiber E (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let o := stdOrthonormalBasis ℝ F
  let c := o.toBasis.map L.toLinearEquiv
  have hc (j k) : B (c j) (c k) = if j = k then 1 else 0 := o.inner_eq_ite j k
  have hl := Positive.MetricTrace.bilinearMetric_trace_orthogonal B hpos b c hc (CovectorTensorAlgebra.covectorTensorRealBilinear b n B N P)
  have hr := Positive.MetricTrace.bilinearMetric_trace_orthogonal B hpos b c hc (CovectorTensorAlgebra.covectorTensorRealBilinear b n B P N)
  simp only [CovectorTensorAlgebra.covectorTensorRealBilinear, LinearMap.mk₂_apply] at hl hr
  simp only [CovectorTensorAlgebra.covectorTensorMetricPair, Complex.re_sum]
  rw [hl, hr]
  apply Finset.sum_congr rfl
  intro j _
  have hs := congrArg Complex.re (Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_symm b n B hB hpos (N (c j)) (P (c j)))
  simpa only [Complex.star_def, Complex.conj_re] using hs.symm

end

/-! Strict positivity of the original full covariant tensor metric. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_re_definite (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (ha : (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a a).re = 0) : a = 0 := by
  let F := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.RealMetricFiber E (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let p := Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hpos n a
  have hr : (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair n p p).re = 0 :=
    (congrArg Complex.re (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos a a)).symm.trans ha
  have hp : p = 0 := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_definite n p
    ((Analysis.HodgeTheory.Decomposition.Form.Constructions.formMetricPair_self_re n p).symm.trans ((congrArg (fun r : ℝ => (r : ℂ)) hr).trans Complex.ofReal_zero))
  apply ContinuousAlternatingMap.ext
  intro t
  have ht := congrArg (fun q : Analysis.DifferentialForms.Manifold.Basic.FormValue F n => q (fun j => L.symm (t j))) hp
  change a (fun j => L (L.symm (t j))) = 0 at ht
  simp only [ContinuousLinearEquiv.apply_symm_apply] at ht
  change a t = 0
  exact ht

theorem covectorTensorMetricPair_re_definite (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hN : (CovectorTensorAlgebra.covectorTensorMetricPair b n B N N).re = 0) : N = 0 := by
  let F := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.RealMetricFiber E (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let L := Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.realMetricFiberContinuousEquiv (Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.positiveBilinearCore B hB hpos)
  let o := stdOrthonormalBasis ℝ F
  let c := o.toBasis.map L.toLinearEquiv
  have hc (j k) : B (c j) (c k) = if j = k then 1 else 0 := o.inner_eq_ite j k
  have ht := Positive.MetricTrace.bilinearMetric_trace_orthogonal B hpos b c hc (CovectorTensorAlgebra.covectorTensorRealBilinear b n B N N)
  have htt : (CovectorTensorAlgebra.covectorTensorMetricPair b n B N N).re =
      ∑ j, (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (c j)) (N (c j))).re := by
    simpa only [CovectorTensorAlgebra.covectorTensorMetricPair, Complex.re_sum, CovectorTensorAlgebra.covectorTensorRealBilinear, LinearMap.mk₂_apply] using ht
  have hp (j) : 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (N (c j)) (N (c j))).re := by
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hp j)).mp (htt.symm.trans hN)
  have hn (j) : N (c j) = 0 := bilinearFormMetricPair_re_definite b n B hB hpos _ (hz j (Finset.mem_univ j))
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg N (c.sum_repr v)
  simpa only [map_sum, map_smul, hn, smul_zero, Finset.sum_const_zero, _root_.zero_apply] using hv.symm

theorem covectorTensorMetricPair_re_pos (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (N : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (hN : N ≠ 0) :
    0 < (CovectorTensorAlgebra.covectorTensorMetricPair b n B N N).re :=
  lt_of_le_of_ne (CovectorTensorAlgebra.covectorTensorMetricPair_nonneg b n B hB hpos N)
    (fun hz => hN (covectorTensorMetricPair_re_definite b n B hB hpos N hz.symm))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricRe
