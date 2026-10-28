import OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasis
import OAI.Analysis.HodgeTheory.Decomposition.BivectorContraction

/-! # Lefschetz Symbol -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions

noncomputable section

section

/-! The inverse Kähler bivector contracts genuine alternating covectors.
Its principal commutator is insertion of the complex-rotated metric dual. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

def metricLefschetzContraction (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ) (b : Module.Basis ι ℝ E) :
    DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1) →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  (1 / 2 : ℝ) • BivectorContraction.Constructions.bivectorContraction n
    (fun i => KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (fun i => Complex.I • b i)

theorem metricLefschetzContraction_symbol_zero (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E 1) :
    metricLefschetzContraction 0 B b (SymbolDifferential.Constructions.exteriorDifferentialSymbol 1 ξ a) =
      SymbolDifferential.Constructions.exteriorContraction 0 (Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ) a := by
  change (1 / 2 : ℝ) • BivectorContraction.Constructions.bivectorContraction 0 _ _ (SymbolDifferential.Constructions.exteriorDifferentialSymbol 1 ξ a) = _
  rw [BivectorContraction.Constructions.bivectorContraction_symbol_zero, MetricDualBasis.Constructions.kahlerBivector_contracted_vector B hpos hB hBJ,
    ContractionAlgebra.Constructions.exteriorContraction_smul_vector, smul_smul]
  norm_num

theorem metricLefschetzContraction_symbol (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    metricLefschetzContraction (n + 1) B b (SymbolDifferential.Constructions.exteriorDifferentialSymbol (n + 1 + 1) ξ a) -
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ (metricLefschetzContraction n B b a) =
        SymbolDifferential.Constructions.exteriorContraction (n + 1) (Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ) a := by
  have h := BivectorContraction.Constructions.bivectorContraction_symbol n ξ
    (fun i => KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (fun i => Complex.I • b i) a
  rw [MetricDualBasis.Constructions.kahlerBivector_contracted_vector B hpos hB hBJ, ContractionAlgebra.Constructions.exteriorContraction_smul_vector] at h
  have hh := congrArg (fun q : DifferentialForms.Manifold.Basic.FormValue E (n + 1) => (1 / 2 : ℝ) • q) h
  rw [smul_sub, smul_smul] at hh
  norm_num at hh
  simpa only [metricLefschetzContraction, smul_apply, map_smul] using hh

end

/-! The inverse Kähler commutator with the twisted exterior symbol is
insertion of the original metric dual, in every nonnegative boundary degree. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

omit [Fintype ι] in
theorem complexMetricSharp_twisted (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v)) (ξ : E →L[ℝ] ℝ) :
    Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) =
      KoszulConnection.Constructions.bilinearMetricSharp B ξ := by
  rw [MetricDualBasis.Constructions.bilinearMetricSharp_comp_J B hpos hBJ ξ, smul_neg, smul_smul,
    Complex.I_mul_I, neg_smul, one_smul, neg_neg]

theorem metricLefschetzContraction_twisted_symbol_zero (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E 1) :
    metricLefschetzContraction 0 B b
      (SymbolDifferential.Constructions.exteriorDifferentialSymbol 1 (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) a) =
      SymbolDifferential.Constructions.exteriorContraction 0 (KoszulConnection.Constructions.bilinearMetricSharp B ξ) a := by
  rw [metricLefschetzContraction_symbol_zero B hpos hB hBJ,
    complexMetricSharp_twisted B hpos hBJ]

theorem metricLefschetzContraction_twisted_symbol (n : ℕ) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    metricLefschetzContraction (n + 1) B b
        (SymbolDifferential.Constructions.exteriorDifferentialSymbol (n + 1 + 1) (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) a) -
      SymbolDifferential.Constructions.exteriorDifferentialSymbol n (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))
        (metricLefschetzContraction n B b a) =
      SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp B ξ) a := by
  rw [metricLefschetzContraction_symbol n B hpos hB hBJ,
    complexMetricSharp_twisted B hpos hBJ]

end

end OAI.Analysis.HodgeTheory.Decomposition.LefschetzSymbol.Constructions
