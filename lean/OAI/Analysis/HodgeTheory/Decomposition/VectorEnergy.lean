import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Vector Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorEnergy.Constructions

noncomputable section

/-! Genuine vector-valued H¹ norms controlled by the actual first-derivative energy. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Fintype ι]

theorem vectorSchwartzSobolev_of_energy
    (b : OrthonormalBasis ι ℝ E)
    (f : 𝓢(E, F)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ‖f.toLp 2 volume‖ ^ 2 + (∑ i, ‖(∂_{b i} f).toLp 2 volume‖ ^ 2) ≤ C ^ 2) :
    ‖VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 f‖ ≤
      C * (1 + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Fintype.card ι) := by
  have hnorm : ‖f.toLp 2 volume‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    exact (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans hf
  have hd (i : ι) : ‖(∂_{b i} f).toLp 2 volume‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖(∂_{b j} f).toLp 2 volume‖) (Finset.mem_univ i)
    exact hi.trans ((le_add_of_nonneg_left (sq_nonneg ‖f.toLp 2 volume‖)).trans hf)
  have hsum : (∑ i, ‖(∂_{b i} f).toLp 2 volume‖) ≤ Fintype.card ι * C := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hd i))
  calc
    _ ≤ ‖f.toLp 2 volume‖ + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ∑ i, ‖(∂_{b i} f).toLp 2 volume‖ := VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate_one_bound b f
    _ ≤ C + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (Fintype.card ι * C) :=
      add_le_add hnorm (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ = _ := by ring

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorEnergy.Constructions
