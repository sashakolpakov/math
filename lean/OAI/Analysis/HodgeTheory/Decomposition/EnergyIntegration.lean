import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Energy Integration -/

namespace OAI.Analysis.HodgeTheory.Decomposition.EnergyIntegration.Constructions

noncomputable section

/-! Integration of a bounded principal energy and three genuine L² pairings. -/

open _root_.MeasureTheory
open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction

theorem bounded_energy_three_pairs {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (A : α → G →L[ℝ] G) (hAm : AEStronglyMeasurable A μ) {K : ℝ}
    (hAB : ∀ᵐ x ∂μ, ‖A x‖ ≤ K) (p q B : Lp G 2 μ) (v C E : Lp F 2 μ) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy A hAm hAB p q + inner ℝ B q + inner ℝ C v + inner ℝ E v =
      ∫ x, inner ℝ (A x (p x)) (q x) + inner ℝ (B x) (q x) +
        inner ℝ (C x) (v x) + inner ℝ (E x) (v x) ∂μ := by
  have hP := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_integrable A hAm hAB p q
  have hB := L2.integrable_inner (𝕜 := ℝ) B q
  have hC := L2.integrable_inner (𝕜 := ℝ) C v
  have hE := L2.integrable_inner (𝕜 := ℝ) E v
  have hPB : Integrable (fun x => inner ℝ (A x (p x)) (q x) + inner ℝ (B x) (q x)) μ := hP.add hB
  have hPBC : Integrable (fun x => inner ℝ (A x (p x)) (q x) + inner ℝ (B x) (q x) +
      inner ℝ (C x) (v x)) μ := hPB.add hC
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver.CM.Construction.boundedFieldEnergy_apply, L2.inner_def, L2.inner_def, L2.inner_def,
    ← integral_add hP hB, ← integral_add hPB hC, ← integral_add hPBC hE]

end

end OAI.Analysis.HodgeTheory.Decomposition.EnergyIntegration.Constructions
