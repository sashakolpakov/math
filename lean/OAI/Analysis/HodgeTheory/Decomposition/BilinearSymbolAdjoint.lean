import OAI.Analysis.HodgeTheory.Decomposition.IntrinsicSymbolAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential
import OAI.Analysis.HodgeTheory.Decomposition.BilinearFormMetric
import OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection

/-! # Bilinear Symbol Adjoint -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearSymbolAdjoint.Constructions

noncomputable section

/-! The principal adjoint of the actual exterior symbol for an arbitrary
positive symmetric metric is insertion of its inverse-metric dual. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_exteriorSymbol (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (ξ : E →L[ℝ] ℝ)
    (a : DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) B (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a) c =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp B ξ) c) := by
  let core := ExteriorPair.Constructions.positiveBilinearCore B hB hpos
  let L := ExteriorPair.Constructions.realMetricFiberContinuousEquiv core
  let w := L.symm (KoszulConnection.Constructions.bilinearMetricSharp B ξ)
  have hξ : ξ.comp L.toContinuousLinearMap = innerSL ℝ w := by
    ext v
    change ξ (L v) = B (KoszulConnection.Constructions.bilinearMetricSharp B ξ) (L v)
    exact (KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos ξ (L v)).symm
  have hupper : BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hpos (n + 1) (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a) =
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n (innerSL ℝ w) (BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hpos n a) := by
    change (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ a).compContinuousLinearMap L.toContinuousLinearMap = _
    rw [SymbolDifferential.Constructions.exteriorDifferentialSymbol_pullback, hξ]
    rfl
  have hlower : BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hpos n (SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp B ξ) c) =
      SymbolDifferential.Constructions.exteriorContraction n w (BilinearFormMetric.Constructions.positiveMetricCoordinateForm B hB hpos (n + 1) c) := by
    have h := SymbolDifferential.Constructions.exteriorContraction_pullback n L.toContinuousLinearMap w c
    have hw : L w = KoszulConnection.Constructions.bilinearMetricSharp B ξ := L.apply_symm_apply _
    change (SymbolDifferential.Constructions.exteriorContraction n (L w) c).compContinuousLinearMap L.toContinuousLinearMap = _ at h
    rw [hw] at h
    exact h
  rw [BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b (n + 1) B hB hpos,
    BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos, hupper, hlower, IntrinsicSymbolAdjoint.Constructions.formMetricPair_exteriorSymbol_inner]

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearSymbolAdjoint.Constructions
