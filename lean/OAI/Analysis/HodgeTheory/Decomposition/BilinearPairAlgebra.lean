import OAI.Analysis.HodgeTheory.Decomposition.BilinearMetricInner
import OAI.Analysis.HodgeTheory.Decomposition.BilinearSymbolAdjoint

/-! # Bilinear Pair Algebra -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions

noncomputable section

/-! Linear pairing rules for the explicit metric on alternating covectors. -/

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem bilinearFormMetricPair_add_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c d : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a + c) d =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a d + BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c d := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_add, inner_add_left]

theorem bilinearFormMetricPair_sub_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c d : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a - c) d =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a d - BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c d := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_sub, inner_sub_left]

theorem bilinearFormMetricPair_neg_left (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (-a) c = -BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_neg, inner_neg_left]

theorem bilinearFormMetricPair_neg_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (-c) = -BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_neg, inner_neg_right]

theorem bilinearFormMetricPair_sum_left [Fintype κ] (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : κ → DifferentialForms.Manifold.Basic.FormValue E n) (c : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (∑ i, a i) c = ∑ i, BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (a i) c := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_sum, sum_inner]

theorem bilinearFormMetricPair_sum_right [Fintype κ] (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E n) (c : κ → DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (∑ i, c i) = ∑ i, BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (c i) := by
  simp only [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, map_sum, inner_sum]

theorem bilinearFormMetricPair_real_smul_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a c : DifferentialForms.Manifold.Basic.FormValue E n) (t : ℝ) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a (t • c) = t • BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  rw [BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner, BilinearMetricInner.Constructions.bilinearFormMetricPair_eq_inner]
  have hQ := ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).toContinuousLinearMap.restrictScalars ℝ).map_smul t c
  change SymbolDifferential.Constructions.exteriorCoordinateEquiv b n (t • c) = t • SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c at hQ
  rw [hQ, inner_smul_right_eq_smul]

theorem bilinearFormMetricPair_symm (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (a c : DifferentialForms.Manifold.Basic.FormValue E n) :
    star (BilinearFormMetric.Constructions.bilinearFormMetricPair b n B c a) = BilinearFormMetric.Constructions.bilinearFormMetricPair b n B a c := by
  simp only [BilinearFormMetric.Constructions.bilinearFormMetricPair_eq_intrinsic b n B hB hpos]
  exact ExteriorPair.Constructions.formMetricPair_symm n _ _

theorem bilinearFormMetricPair_exteriorSymbol_right (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hB : ∀ u v, B u v = B v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (ξ : E →L[ℝ] ℝ)
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1)) (c : DifferentialForms.Manifold.Basic.FormValue E n) :
    BilinearFormMetric.Constructions.bilinearFormMetricPair b (n + 1) B a (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ c) =
      BilinearFormMetric.Constructions.bilinearFormMetricPair b n B (SymbolDifferential.Constructions.exteriorContraction n (KoszulConnection.Constructions.bilinearMetricSharp B ξ) a) c := by
  rw [← bilinearFormMetricPair_symm b (n + 1) B hB hpos,
    BilinearSymbolAdjoint.Constructions.bilinearFormMetricPair_exteriorSymbol b n B hB hpos ξ,
    bilinearFormMetricPair_symm b n B hB hpos]

end

end OAI.Analysis.HodgeTheory.Decomposition.BilinearPairAlgebra.Constructions
