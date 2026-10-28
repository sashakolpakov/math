import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.QuadraticLower
import OAI.AlgebraicGeometry.DivisorClass.Chern.TensorMetricUniformLower
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator

/-! # Covector Metric Cutoff Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricCutoffBound

noncomputable section

section

/-! Uniform upper metric bounds and the two-term quadratic estimate for actual covectors. -/

open Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E D ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem bilinearFormMetricPair_add_self_le (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a + c) (a + c)).re ≤
      2 * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a a).re + 2 * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c c).re := by
  have hp : 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a - c) (a - c)).re := by
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n _
  simp only [sub_eq_add_neg, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, Line.ConnectionOperator.bilinearFormMetricPair_add_right,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_left, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_neg_right, Complex.add_re, Complex.neg_re] at hp ⊢
  linarith

theorem bilinearFormMetricPair_uniform_upper (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : D → E →L[ℝ] E →L[ℝ] ℝ) {U K : Set D} (hB : ContDiffOn ℝ ∞ B U)
    (hBs : ∀ x ∈ U, ∀ v t, B x v t = B x t v)
    (hpos : ∀ x ∈ U, ∀ v : E, v ≠ 0 → 0 < B x v v) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n,
      (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) a a).re ≤ C * ‖a‖ ^ 2 := by
  let : FiniteDimensional ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateLinearEquiv b n).symm.finiteDimensional
  let : FiniteDimensional ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := FiniteDimensional.trans ℝ ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
  have hs : ContDiffOn ℝ ∞
      (fun p : D × Analysis.DifferentialForms.Manifold.Basic.FormValue E n => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B p.1) p.2 p.2) (U ×ˢ univ) :=
    Analysis.HodgeTheory.Decomposition.BilinearFormMetricSmooth.Constructions.bilinearFormMetricPair_smoothOn b n (fun p : D × Analysis.DifferentialForms.Manifold.Basic.FormValue E n => B p.1) Prod.snd Prod.snd
      (hB.comp contDiffOn_fst (fun _ hp => hp.1)) contDiffOn_snd contDiffOn_snd
      (fun _ hp => Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B _) (hBs _ hp.1) (hpos _ hp.1))
  apply Compact.QuadraticLower.quadratic_uniform_upper (fun x a => (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) a a).re) hK
    ((Complex.continuous_re.comp_continuousOn hs.continuousOn).mono (fun _ hp => ⟨hKU hp.1, hp.2⟩))
  · intro x _
    simp only [Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_zero, inner_zero_right, Complex.zero_re]
  · intro x _ r a
    rw [Line.TensorMetricTest.bilinearFormMetricPair_real_smul_left, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_real_smul_right]
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

end

/-! The actual metric quadratic estimate for a cutoff product and its commutator term. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_smul_self_re (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (g : ℂ) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (g • a) (g • a)).re = ‖g‖ ^ 2 * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a a).re := by
  rw [Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_left, Line.ConnectionOperator.bilinearFormMetricPair_complex_smul_right,
    ← mul_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.normSq_eq_norm_sq]

theorem bilinearFormMetricPair_cutoff_bound (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ v w, B v w = B w v)
    (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E 1) (c d : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (g : ℂ)
    (C K : ℝ) (hc : (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c c).re ≤ C * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re)
    (hg : ‖g‖ ^ 2 ≤ K) :
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (c + g • d) (c + g • d)).re ≤
      (2 * C) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b 1 B a a).re + (2 * K) * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B d d).re := by
  have hd : 0 ≤ (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B d d).re := by
    rw [Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos]
    exact Analysis.HodgeTheory.Decomposition.ExteriorPair.Constructions.formMetricPair_nonneg n _
  have hi := bilinearFormMetricPair_add_self_le b n B hB hpos c (g • d)
  rw [bilinearFormMetricPair_smul_self_re] at hi
  have hs := add_le_add (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg hd) (by norm_num : (0 : ℝ) ≤ 2))
  exact hi.trans (hs.trans_eq (by ring))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricCutoffBound
