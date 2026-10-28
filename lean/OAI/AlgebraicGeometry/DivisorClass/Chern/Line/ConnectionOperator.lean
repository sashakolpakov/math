import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols

/-! # Connection Operator -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator

noncomputable section

section

/-! Differentiation of the actual covector metric including the line weight and its connection. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormed Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialBilinearNormedSpace
  Analysis.HodgeTheory.Decomposition.BilinearMetricDifferential.Constructions.metricDifferentialCovectorPairNormedSpace

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_complex_smul_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (z • a) c = conj z * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  unfold Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul, star_mul, Complex.star_def]
  ring

omit [FiniteDimensional ℝ E] in
theorem bilinearFormMetricPair_complex_smul_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (z : ℂ) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (z • c) = z * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  unfold Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  ring

theorem bilinearFormMetricPair_add_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c d : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (c + d) = Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c + Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a d := by
  simp only [Analysis.HodgeTheory.Decomposition.BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_add, inner_add_right]

theorem lineMetricPair_covariant_derivative (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (w : E → ℂ) (a c : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x v : E)
    (hB : DifferentiableAt ℝ B x) (hw : DifferentiableAt ℝ w x)
    (ha : DifferentiableAt ℝ a x) (hc : DifferentiableAt ℝ c x)
    (hBs : ∀ u t, B x u t = B x t u) (hpos : ∀ u : E, u ≠ 0 → 0 < B x u u)
    (hΓ : ∀ u t, B x (Γ x v u) t + B x u (Γ x v t) = fderiv ℝ B x v u t)
    (hA : fderiv ℝ w x v = w x * (conj (A x v) + A x v)) :
    fderiv ℝ (fun y => w y * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y)) x v =
      w x * (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (ConnectionSymbols.lineCovectorConnectionDerivative n Γ A a x v) (c x) +
        Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (a x) (ConnectionSymbols.lineCovectorConnectionDerivative n Γ A c x v)) := by
  have hp := Analysis.HodgeTheory.Decomposition.WeightedMetricDerivative.Constructions.bilinearFormMetricPair_differentiableAt b n B a c hB ha hc
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearExteriorGram_det_ne_zero b n (B x) hBs hpos)
  have hd := congrArg (fun L : E →L[ℝ] ℂ => L v) (hw.hasFDerivAt.mul hp.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => w y * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B y) (a y) (c y)) x v = _ at hd
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul] at hd
  rw [Analysis.HodgeTheory.Decomposition.CovectorMetricDifferential.Constructions.bilinearFormMetricPair_covariant_derivative b n B Γ a c x v hB ha hc hBs hpos hΓ, hA] at hd
  rw [hd, ConnectionSymbols.lineCovectorConnectionDerivative_apply, ConnectionSymbols.lineCovectorConnectionDerivative_apply,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_add_left, bilinearFormMetricPair_add_right,
    bilinearFormMetricPair_complex_smul_left, bilinearFormMetricPair_complex_smul_right]
  ring

end

section

/-! The line-connection terms in exterior differentiation and the metric trace are exact adjoint symbols. -/

open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem lineConnectionTerm_alternation (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    ContinuousAlternatingMap.alternatizeUncurryFin (ConnectionSymbols.lineConnectionTerm n A a) =
      ∑ i, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap (A (b i) • a) := by
  have hd := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.derivative_basis_expansion b n (ConnectionSymbols.lineConnectionTerm n A a)
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ (ConnectionSymbols.lineConnectionTerm n A a) = _
  rw [hd, map_sum]
  rfl

omit [LinearOrder ι] in
theorem lineCovariantCodifferential_expansion (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (x : E) :
    ConnectionSymbols.lineCovariantCodifferential b n B Γ A a x = Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions.bilinearCovariantCodifferential b n B Γ a x -
      ∑ i, A x (b i) • Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x) := by
  simp only [ConnectionSymbols.lineCovariantCodifferential, ConnectionSymbols.lineCovectorConnectionDerivative_apply, map_add,
    ConnectionSymbols.exteriorContraction_complex_smul, Finset.sum_add_distrib, Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions.bilinearCovariantCodifferential]
  abel

theorem lineConnectionTerm_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hBs : ∀ v w, B v w = B w v) (hpos : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) B a (ContinuousAlternatingMap.alternatizeUncurryFin (ConnectionSymbols.lineConnectionTerm n A c)) =
      ∑ i, A (b i) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n B
        (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) a) c := by
  rw [lineConnectionTerm_alternation b n A c, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Analysis.HodgeTheory.Decomposition.ComplexMetric.Constructions.exteriorDifferentialSymbol_complex_smul, bilinearFormMetricPair_complex_smul_right,
    Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_exteriorSymbol_right b n B hBs hpos]

theorem lineCovariantCodifferential_pair (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (ConnectionSymbols.lineCovariantCodifferential b n B Γ A a x) c =
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x) (Analysis.HodgeTheory.Decomposition.CovariantAdjointPair.Constructions.bilinearCovariantCodifferential b n B Γ a x) c -
        ∑ i, conj (A x (b i)) * Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair b n (B x)
          (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorContraction n (Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (B x) (b.coord i).toContinuousLinearMap) (a x)) c := by
  rw [lineCovariantCodifferential_expansion, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sub_left, Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions.bilinearFormMetricPair_sum_left]
  simp_rw [bilinearFormMetricPair_complex_smul_left]

end

section

/-! The actual exterior line-connection term as a continuous matrix operator in fixed form coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def lineConnectionSymbol (b : Module.Basis ι ℝ E) (n : ℕ) (A : E →L[ℝ] ℂ) :
    Analysis.DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E (n + 1) :=
  ∑ i, (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap).comp
    (ContinuousLinearMap.lsmul ℝ ℂ (A (b i)))

omit [LinearOrder ι] in
theorem lineConnectionSymbol_apply (b : Module.Basis ι ℝ E) (n : ℕ) (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    lineConnectionSymbol b n A a = ContinuousAlternatingMap.alternatizeUncurryFin (ConnectionSymbols.lineConnectionTerm n A a) := by
  rw [lineConnectionTerm_alternation b n A a]
  simp only [lineConnectionSymbol, _root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply]

def lineConnectionCoordinateOperator (b : Module.Basis ι ℝ E) (n : ℕ) (A : E →L[ℝ] ℂ) :
    Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1) :=
  ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)).toContinuousLinearMap.restrictScalars ℝ).comp
    ((lineConnectionSymbol b n A).comp ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ))

theorem lineConnectionCoordinateOperator_apply (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    lineConnectionCoordinateOperator b n A (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a) =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
        (ContinuousAlternatingMap.alternatizeUncurryFin (ConnectionSymbols.lineConnectionTerm n A a)) := by
  change Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
    (lineConnectionSymbol b n A ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv b n a))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, lineConnectionSymbol_apply]

end

/-! Smoothness of the actual line-connection matrices and their native real adjoints. -/

open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E D ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem lineConnectionSymbol_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : D → E →L[ℝ] ℂ) {U : Set D} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => lineConnectionSymbol b n (A x)) U := by
  apply ContDiffOn.sum
  intro i _
  have hl (z : ℂ) : ContinuousLinearMap.lsmul ℝ ℂ (E := Analysis.DifferentialForms.Manifold.Basic.FormValue E n) z =
      z • ContinuousLinearMap.id ℝ (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) := by ext a; rfl
  simp_rw [hl]
  exact contDiffOn_const.clm_comp
    ((hA.clm_apply (contDiffOn_const (c := b i))).smul contDiffOn_const)

theorem lineConnectionCoordinateOperator_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : D → E →L[ℝ] ℂ) {U : Set D} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => lineConnectionCoordinateOperator b n (A x)) U :=
  contDiffOn_const.clm_comp ((lineConnectionSymbol_smoothOn b n A hA).clm_comp contDiffOn_const)

theorem lineConnectionCoordinateAdjoint_smoothOn (b : Module.Basis ι ℝ E) (n : ℕ)
    (A : D → E →L[ℝ] ℂ) {U : Set D} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun x => (lineConnectionCoordinateOperator b n (A x)).adjoint) U :=
  (ContinuousLinearMap.adjoint : (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1)) ≃ₗᵢ[ℝ]
    (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1) →L[ℝ] Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)).toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (lineConnectionCoordinateOperator_smoothOn b n A hA)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionOperator
