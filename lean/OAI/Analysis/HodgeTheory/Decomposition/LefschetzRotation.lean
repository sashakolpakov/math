import OAI.Analysis.HodgeTheory.Decomposition.BivectorCovectorAction
import OAI.Analysis.HodgeTheory.Decomposition.BivectorBasisTransport
import OAI.Analysis.HodgeTheory.Decomposition.MetricCovariantInsertion

/-! # Lefschetz Rotation -/

namespace OAI.Analysis.HodgeTheory.Decomposition.LefschetzRotation.Constructions

noncomputable section

/-! Inverse Kähler contraction commutes with infinitesimal complex rotation
on the actual alternating covectors. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype ι]

theorem kahlerBivector_rotation_balance (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    BivectorContraction.Constructions.bivectorContraction n (fun i => Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)
        (fun i => Complex.I • b i) a +
      BivectorContraction.Constructions.bivectorContraction n (fun i => KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)
        (fun i => Complex.I • (Complex.I • b i)) a = 0 := by
  have h := BivectorBasisTransport.Constructions.bivector_basis_transport b n (KoszulConnection.Constructions.bilinearMetricSharp B)
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a
  change (∑ i, SymbolDifferential.Constructions.exteriorContraction n (Complex.I • b i)
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp B
        ((b.coord i).toContinuousLinearMap.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) a)) =
    ∑ i, SymbolDifferential.Constructions.exteriorContraction n (Complex.I • (Complex.I • b i))
      (SymbolDifferential.Constructions.exteriorContraction (n + 1) (KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) a) at h
  simp only [MetricDualBasis.Constructions.bilinearMetricSharp_comp_J B hpos hBJ, MetricCovariantInsertion.Constructions.exteriorContraction_neg_vector, map_neg,
    Finset.sum_neg_distrib] at h
  simp only [BivectorContraction.Constructions.bivectorContraction_apply]
  rw [← h]
  exact add_neg_cancel _

theorem metricLefschetzContraction_rotation (b : Module.Basis ι ℝ E) (n : ℕ)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (a : DifferentialForms.Manifold.Basic.FormValue E (n + 1 + 1)) :
    LefschetzSymbol.Constructions.metricLefschetzContraction n B b
      (CovectorConnection.Constructions.covectorInfinitesimalAction (n + 1 + 1) (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a) =
    CovectorConnection.Constructions.covectorInfinitesimalAction n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
      (LefschetzSymbol.Constructions.metricLefschetzContraction n B b a) := by
  have h := BivectorCovectorAction.Constructions.bivectorContraction_covectorAction n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)
    (fun i => KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (fun i => Complex.I • b i) a
  have hz := kahlerBivector_rotation_balance b n B hpos hBJ a
  change _ = _ + BivectorContraction.Constructions.bivectorContraction n
    (fun i => Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) (fun i => Complex.I • b i) a +
    BivectorContraction.Constructions.bivectorContraction n (fun i => KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)
      (fun i => Complex.I • (Complex.I • b i)) a at h
  have hassoc (f g k : DifferentialForms.Manifold.Basic.FormValue E n) : f + g + k = f + (g + k) := add_assoc f g k
  rw [hassoc, hz, add_zero] at h
  simp only [LefschetzSymbol.Constructions.metricLefschetzContraction, smul_apply, map_smul]
  exact congrArg (fun f : DifferentialForms.Manifold.Basic.FormValue E n => (1 / 2 : ℝ) • f) h

end

end OAI.Analysis.HodgeTheory.Decomposition.LefschetzRotation.Constructions
