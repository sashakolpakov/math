import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator

/-! # Weighted Adjoint -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.WeightedAdjoint

noncomputable section

/-! The actual density-weighted adjoint numerator, including the original line metric and connection terms. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem lineWeightedAdjointPair_derivative_sum (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (w : E → ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) {x : E}
    (hB : DifferentiableAt ℝ B x) (hw : DifferentiableAt ℝ w x) (ha : DifferentiableAt ℝ a x)
    (hρ : DifferentiableAt ℝ (fun y => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y)) x)
    (hBs : ∀ v t, B x v t = B x t v) (hpos : ∀ v : E, v ≠ 0 → 0 < B x v v)
    (hΓ : ∀ u v t, B x (Γ x u v) t + B x v (Γ x u t) = fderiv ℝ B x u v t)
    (hΓs : ∀ u v, Γ x u v = Γ x v u)
    (hA : ∀ v, fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    (∑ i, fderiv ℝ (fun y => w y * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c))) x (b i)) =
      w x * (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B x) (a x)
          (ContinuousAlternatingMap.alternatizeUncurryFin (ConnectionSymbols.lineConnectionTerm n (A x) c)) -
          Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (ConnectionSymbols.lineCovariantCodifferential b n B Γ A a x) c) := by
  have hi (i : ι) :
      fderiv ℝ (fun y => w y * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c))) x (b i) =
      w x * fderiv ℝ (fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)) x (b i) +
      w x * (conj (A x (b i)) + A x (b i)) * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B x) (a x)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)) := by
    have hp := Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions.bilinearFormMetricPair_differentiableAt b (n + 1) B a
      (fun _ => Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)
      hB ha (differentiableAt_const _) (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b (n + 1) (B x) hBs hpos)
    have hρc := (Complex.ofRealCLM.hasFDerivAt.comp x hρ.hasFDerivAt).differentiableAt
    have hprod := hρc.mul hp
    have hd := congrArg (fun L : E →L[ℝ] ℂ => L (b i)) (hw.hasFDerivAt.mul hprod.hasFDerivAt).fderiv
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at hd
    change fderiv ℝ (fun y => w y * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c))) x (b i) =
      w x * fderiv ℝ (fun y => (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B y) : ℂ) *
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B y) (a y)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)) x (b i) +
      ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) (B x) (a x)
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap c)) * fderiv ℝ w x (b i) at hd
    rw [hA] at hd
    rw [hd]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_add_distrib, ← Finset.mul_sum,
    Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions.covariantAdjointPair_derivative_sum b n B Γ a c hB ha hρ hBs hpos hΓ hΓs]
  simp_rw [Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_exteriorSymbol_right b n (B x) hBs hpos]
  rw [ConnectionOperator.lineConnectionTerm_pair b n (B x) (A x) (a x) c hBs hpos, ConnectionOperator.lineCovariantCodifferential_pair]
  have hs : (∑ i, w x * (conj (A x (b i)) + A x (b i)) * ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x)) c)) =
      w x * (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.metricDensity b (B x) : ℂ) *
        ((∑ i, conj (A x (b i)) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x)) c) +
         ∑ i, A x (b i) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x)) c) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.WeightedAdjoint
