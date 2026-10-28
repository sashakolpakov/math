import OAI.Analysis.HodgeTheory.Decomposition.ComplexMetric

/-! # Symbol -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Symbol.Constructions

noncomputable section

/-! The linear symbol of the exterior derivative is the sum of its actual
constant directional symbols in any fixed basis. -/

open scoped BigOperators

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

omit [LinearOrder ι] in
theorem exteriorSymbol_basis (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) :
    SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a =
      ∑ i, ξ (b i) • SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap a := by
  have h := congrArg (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (SymbolDifferential.Constructions.derivative_basis_expansion b n (ξ.smulRight a))
  rw [map_sum] at h
  change SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
    ((b.coord i).toContinuousLinearMap.smulRight (ξ (b i) • a)) =
      ξ (b i) • ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
        ((b.coord i).toContinuousLinearMap.smulRight a)
  rw [← map_smul]
  congr 1
  apply ContinuousLinearMap.ext
  intro v
  change (b.coord i) v • (ξ (b i) • a) = ξ (b i) • ((b.coord i) v • a)
  exact smul_comm _ _ _

theorem coordinateCovectorSymbol_basis (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) (a : SymbolDifferential.Constructions.ExteriorCoordinates ι n) :
    SymbolEllipticity.Constructions.coordinateCovectorSymbol b n ξ a =
      ∑ i, ξ (b i) • SymbolEllipticity.Constructions.coordinateCovectorSymbol b n (b.coord i).toContinuousLinearMap a := by
  change SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
    (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm a)) = _
  rw [exteriorSymbol_basis b n ξ, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)).toContinuousLinearMap.restrictScalars ℝ).map_smul
    (ξ (b i)) (SymbolDifferential.Constructions.exteriorDifferentialSymbol n (b.coord i).toContinuousLinearMap ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm a))

end

end OAI.Analysis.HodgeTheory.Decomposition.Symbol.Constructions
