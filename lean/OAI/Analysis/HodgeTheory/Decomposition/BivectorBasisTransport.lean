import OAI.Analysis.HodgeTheory.Decomposition.LefschetzSymbol

/-! # Bivector Basis Transport -/

namespace OAI.Analysis.HodgeTheory.Decomposition.BivectorBasisTransport.Constructions

noncomputable section

/-! Moving a tangent endomorphism between the two factors of an inverse
metric contraction by the actual basis-dual expansion. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem bivector_basis_transport (b : Module.Basis ι ℝ E) (n : ℕ)
    (S : (E →L[ℝ] ℝ) →L[ℝ] E) (J A : E →L[ℝ] E) (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    (∑ i, SymbolDifferential.Constructions.exteriorContraction n (J (b i))
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (S ((b.coord i).toContinuousLinearMap.comp A)) a)) =
    ∑ i, SymbolDifferential.Constructions.exteriorContraction n (J (A (b i)))
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (S (b.coord i).toContinuousLinearMap) a) := by
  have hS (i : ι) : S ((b.coord i).toContinuousLinearMap.comp A) =
      ∑ j, b.repr (A (b j)) i • S (b.coord j).toContinuousLinearMap := by
    have h := congrArg S (MetricDualBasis.Constructions.continuousCovector_basis_expansion b ((b.coord i).toContinuousLinearMap.comp A))
    simp only [map_sum, map_smul, ContinuousLinearMap.comp_apply] at h
    change S ((b.coord i).toContinuousLinearMap.comp A) =
      ∑ j, b.repr (A (b j)) i • S (b.coord j).toContinuousLinearMap at h
    exact h
  simp_rw [hS, BivectorContraction.Constructions.exteriorContraction_sum_vector, map_sum, ContractionAlgebra.Constructions.exteriorContraction_smul_vector, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hv : (∑ i, b.repr (A (b j)) i • J (b i)) = J (A (b j)) := by
    simpa only [map_sum, map_smul] using congrArg J (b.sum_repr (A (b j)))
  rw [← hv, BivectorContraction.Constructions.exteriorContraction_sum_vector]
  simp only [ContractionAlgebra.Constructions.exteriorContraction_smul_vector]

end

end OAI.Analysis.HodgeTheory.Decomposition.BivectorBasisTransport.Constructions
