import OAI.Analysis.HodgeTheory.Decomposition.SymbolEllipticity

/-! # Complex Metric -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric.Constructions

noncomputable section

section

/-! Complex-linear versions of the actual exterior symbols, needed for
their Fourier-transform identities. -/

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exteriorDifferentialSymbol_complex_smul (n : ℕ) (ξ : E →L[ℝ] ℝ)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (c : ℂ) :
    SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (c • a) = c • SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a := by
  ext v
  change SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (c • a) v = c • SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a v
  rw [SymbolDifferential.Constructions.exteriorDifferentialSymbol_apply, SymbolDifferential.Constructions.exteriorDifferentialSymbol_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (-1 : ℤ) ^ (i : ℕ) • (ξ (v i) • (c • a (i.removeNth v))) =
    c • ((-1 : ℤ) ^ (i : ℕ) • (ξ (v i) • a (i.removeNth v)))
  rw [smul_comm (ξ (v i)) c, smul_comm ((-1 : ℤ) ^ (i : ℕ)) c]

variable [FiniteDimensional ℝ E] {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem coordinateCovectorSymbol_complex_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) (a : SymbolDifferential.Constructions.ExteriorCoordinates ι n) (c : ℂ) :
    SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ (c • a) = c • SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ a := by
  change SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
    (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (c • a))) =
      c • SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
        (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm a))
  rw [map_smul, exteriorDifferentialSymbol_complex_smul, map_smul]

/-- The Fourier-compatible symbol has exactly the values of the derived real-coordinate symbol. -/
def coordinateComplexSymbol (b : Module.Basis ι ℝ E) (n : ℕ) (ξ : E →L[ℝ] ℝ) :
    SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℂ] SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1) :=
  { toLinearMap :=
      { toFun := SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ
        map_add' := (SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ).map_add
        map_smul' := fun c a => coordinateCovectorSymbol_complex_smul b n ξ a c }
    cont := (SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ).continuous }

theorem coordinateComplexSymbol_restrictScalars (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) :
    (coordinateComplexSymbol b n ξ).restrictScalars ℝ = SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ := by
  apply ContinuousLinearMap.ext
  intro a
  rfl

end

/-! Complex linearity of the metric operators and compatibility of the
real and complex Hilbert adjoints in the genuine Euclidean coordinates. -/

section Matrices

variable {I J : Type*} [Fintype I] [Fintype J]

def complexMatrixOperator (A : Matrix I I ℝ) : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  ∑ s, ∑ t, (A s t : ℂ) • InnerProductSpace.rankOne ℂ
    (EuclideanSpace.basisFun I ℂ s) (EuclideanSpace.basisFun I ℂ t)

theorem complexMatrixOperator_restrictScalars (A : Matrix I I ℝ) :
    (complexMatrixOperator A).restrictScalars ℝ = CoordinateMetric.Constructions.realMatrixOperator A := by
  apply ContinuousLinearMap.ext
  intro u
  change complexMatrixOperator A u = CoordinateMetric.Constructions.realMatrixOperator A u
  simp only [complexMatrixOperator, CoordinateMetric.Constructions.realMatrixOperator, sum_apply, smul_apply]
  rfl

theorem realMatrixOperator_complex_smul (A : Matrix I I ℝ) (u : EuclideanSpace ℂ I) (c : ℂ) :
    CoordinateMetric.Constructions.realMatrixOperator A (c • u) = c • CoordinateMetric.Constructions.realMatrixOperator A u := by
  rw [← complexMatrixOperator_restrictScalars]
  exact (complexMatrixOperator A).map_smul c u

theorem euclidean_adjoint_restrictScalars (A : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (A.restrictScalars ℝ).adjoint = A.adjoint.restrictScalars ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ u (A v) = inner ℝ (A.adjoint u) v
  rw [CoordinateMetric.Constructions.euclidean_real_inner_eq_re, CoordinateMetric.Constructions.euclidean_real_inner_eq_re, ContinuousLinearMap.adjoint_inner_left]

end Matrices

section Inverse

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem inverse_complex_smul (A : F →L[ℝ] F) (hA : A.IsInvertible)
    (hℂ : ∀ (c : ℂ) (u : F), A (c • u) = c • A u) (c : ℂ) (u : F) :
    A.inverse (c • u) = c • A.inverse u := by
  apply hA.injective
  rw [hA.self_apply_inverse, hℂ, hA.self_apply_inverse]

end Inverse

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ)

theorem projectiveWeightedFormOperator_complex_smul (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (c : ℂ) (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z (c • u) = c • AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z u := by
  change AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • (CoordinateMetric.Constructions.realMatrixOperator _ (c • u)) =
    c • (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • CoordinateMetric.Constructions.realMatrixOperator _ u)
  rw [realMatrixOperator_complex_smul, smul_comm]

theorem projectiveWeightedFormOperator_inverse_complex_smul
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (c : ℂ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse (c • u) =
      c • (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z).inverse u :=
  inverse_complex_smul _ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_isInvertible V e he n z hz)
    (projectiveWeightedFormOperator_complex_smul V e n z) c u

end

end OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric.Constructions
