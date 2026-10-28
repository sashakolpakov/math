import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv
import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceConvergence
import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange
import OAI.Analysis.HodgeTheory.Decomposition.VectorLocalElliptic

/-! # Vector Strong Sobolev -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorStrongSobolev.Constructions

noncomputable section

/-! The recursive strong-derivative description is equivalent to the native
distributional Sobolev regularity for the actual complex Hilbert-valued L² functions. -/

open _root_.MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [InnerProductSpace ℝ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F]

theorem vectorStrongSobolev_succ_is_h1 (b : OrthonormalBasis ι ℝ E) {n : ℕ}
    {u : Lp F 2 (volume : Measure E)} (hu : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b (n + 1) u) :
    MemSobolev 1 2 (u : 𝓢'(E, F)) := by
  apply VectorDifferenceCriterion.Constructions.vectorMemSobolev_one_of_difference_bounds b
  intro i
  obtain ⟨_, _, ⟨B, hB⟩, _⟩ := hu.2 i
  refine ⟨B, Filter.Eventually.of_forall (fun t => ?_)⟩
  rw [← VectorLocalElliptic.Constructions.realL2Difference_eq_vector]
  exact hB t

theorem vectorStrongSobolev_iff_memSobolev (b : OrthonormalBasis ι ℝ E) (n : ℕ)
    (u : Lp F 2 (volume : Measure E)) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u ↔ MemSobolev (n : ℝ) 2 (u : 𝓢'(E, F)) := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.cast_zero, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolev.CM.Construction.HasStrongSobolevDerivatives, true_iff]
    exact memSobolev_zero_iff.mpr ⟨u, rfl⟩
  | succ n ih =>
    constructor
    · intro hu
      obtain ⟨w, hw⟩ := (VectorEmbeddingRange.Constructions.vectorMemSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp
        (vectorStrongSobolev_succ_is_h1 b hu)
      rw [Nat.cast_succ]
      apply (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b (n : ℝ) (u : 𝓢'(E, F))).mpr
      refine ⟨(ih u).mp hu.1, fun i => ?_⟩
      obtain ⟨du, hdu, _, hduN⟩ := hu.2 i
      have hknown := VectorDifferenceConvergence.Constructions.vectorL2DifferenceQuotient_tendsto_derivative (b i) w
      rw [hw] at hknown
      have hdu' : Tendsto (fun t : ℝ => VectorDifferences.Constructions.vectorL2DifferenceQuotient (b i) t u) (𝓝[≠] 0) (𝓝 du) := by
        simpa only [VectorLocalElliptic.Constructions.realL2Difference_eq_vector] using hdu
      have heq := tendsto_nhds_unique hdu' hknown
      have hdistr : (du : 𝓢'(E, F)) = ∂_{b i} (u : 𝓢'(E, F)) := by
        rw [heq, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, hw]
      rw [← hdistr]
      exact (ih du).mp hduN
    · intro hu
      have hu1 : MemSobolev 1 2 (u : 𝓢'(E, F)) :=
        hu.mono (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
      obtain ⟨w, hw⟩ := (VectorEmbeddingRange.Constructions.vectorMemSobolev_l2_iff_embedding_range (by norm_num : (0 : ℝ) ≤ 1) u).mp hu1
      rw [Nat.cast_succ] at hu
      have hp := (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv.CM.Construction.memSobolev_succ_iff_derivatives b (n : ℝ) (u : 𝓢'(E, F))).mp hu
      refine ⟨(ih u).mpr hp.1, fun i =>
        ⟨AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) w, ?_, ⟨(2 * Real.pi * ‖b i‖) * ‖w‖, fun t => ?_⟩, ?_⟩⟩
      · simpa only [VectorLocalElliptic.Constructions.realL2Difference_eq_vector, hw] using
          VectorDifferenceConvergence.Constructions.vectorL2DifferenceQuotient_tendsto_derivative (b i) w
      · rw [VectorLocalElliptic.Constructions.realL2Difference_eq_vector, ← hw]
        exact VectorDifferenceBounds.Constructions.vectorL2DifferenceQuotient_sobolev_bound (b i) t w
      · apply (ih _).mpr
        rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevDifferential.CM.Construction.sobolevL2Derivative_distribution, hw]
        exact hp.2 i

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorStrongSobolev.Constructions
