import OAI.Analysis.HodgeTheory.Decomposition.KoszulConnection
import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential

/-! # Metric Dual Basis -/

namespace OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions

noncomputable section

/-! Metric-dual basis formulas and the exact behavior of the sharp map
under the compatible complex structure. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι]

theorem continuousCovector_basis_expansion (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) :
    ξ = ∑ i, ξ (b i) • (b.coord i).toContinuousLinearMap := by
  ext v
  simp only [sum_apply, smul_apply, smul_eq_mul]
  have h := congrArg ξ (b.sum_repr v)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  change ξ v = ∑ i, ξ (b i) * b.repr v i
  simpa only [mul_comm] using h.symm

theorem bilinearMetricSharp_dual_expansion (B : E →L[ℝ] E →L[ℝ] ℝ)
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) :
    (∑ i, ξ (b i) • KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) = KoszulConnection.Constructions.bilinearMetricSharp B ξ := by
  calc
    _ = KoszulConnection.Constructions.bilinearMetricSharp B (∑ i, ξ (b i) • (b.coord i).toContinuousLinearMap) := by
      rw [map_sum]
      simp only [map_smul]
    _ = KoszulConnection.Constructions.bilinearMetricSharp B ξ := congrArg (KoszulConnection.Constructions.bilinearMetricSharp B) (continuousCovector_basis_expansion b ξ).symm

theorem bilinearMetricSharp_basis_expansion (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) :
    (∑ i, ξ (KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) • b i) = KoszulConnection.Constructions.bilinearMetricSharp B ξ := by
  have hcoeff (i : ι) : ξ (KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) = b.repr (KoszulConnection.Constructions.bilinearMetricSharp B ξ) i := by
    rw [← KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos ξ, hB, KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos]
    rfl
  simp only [hcoeff]
  exact b.sum_repr _

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

omit [Fintype ι] in
theorem bilinearMetricSharp_comp_J (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v)) (ξ : E →L[ℝ] ℝ) :
    KoszulConnection.Constructions.bilinearMetricSharp B (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) =
      -(Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ) := by
  apply KoszulConnection.Constructions.positive_bilinear_left_ext B hpos
  intro w
  rw [KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos, map_neg, neg_apply, hBJ,
    KoszulConnection.Constructions.bilinearMetricSharp_pair B hpos, neg_neg]
  rfl

theorem kahlerBivector_contracted_vector (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hpos : ∀ u : E, u ≠ 0 → 0 < B u u) (hB : ∀ u v, B u v = B v u)
    (hBJ : ∀ u v, B (Complex.I • u) v = -B u (Complex.I • v))
    (b : Module.Basis ι ℝ E) (ξ : E →L[ℝ] ℝ) :
    (∑ i, (ξ (KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) • (Complex.I • b i) -
      ξ (Complex.I • b i) • KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap)) =
        (2 : ℝ) • (Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ) := by
  have hfirst : (∑ i, ξ (KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) • (Complex.I • b i)) =
      Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ := by
    simp_rw [smul_comm (ξ _) Complex.I]
    rw [← Finset.smul_sum, bilinearMetricSharp_basis_expansion B hpos hB b ξ]
  have hsecond : (∑ i, ξ (Complex.I • b i) • KoszulConnection.Constructions.bilinearMetricSharp B (b.coord i).toContinuousLinearMap) =
      -(Complex.I • KoszulConnection.Constructions.bilinearMetricSharp B ξ) :=
    (bilinearMetricSharp_dual_expansion B b (ξ.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))).trans
      (bilinearMetricSharp_comp_J B hpos hBJ ξ)
  rw [Finset.sum_sub_distrib, hfirst, hsecond, sub_neg_eq_add, two_smul]

end

end OAI.Analysis.HodgeTheory.Decomposition.MetricDualBasis.Constructions
