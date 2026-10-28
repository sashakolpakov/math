import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential

/-! # Pair Locality -/

namespace OAI.Analysis.HodgeTheory.Decomposition.PairLocality.Constructions

noncomputable section

/-! Actual L² coefficient pairings only use values on the support of the
test field, and a cutoff equal to one there preserves those values. -/

open _root_.MeasureTheory
open scoped SchwartzMap

theorem lp_field_pair_eq_of_local_eq {α F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (B : α → F → G) (M : Lp F 2 μ → Lp G 2 μ)
    (u u' : Lp F 2 μ) (v : Lp G 2 μ) (S : Set α)
    (hM : ∀ w, M w =ᵐ[μ] fun x => B x (w x))
    (hu : ∀ᵐ x ∂μ, x ∈ S → u x = u' x)
    (hv : ∀ᵐ x ∂μ, x ∉ S → v x = 0) :
    inner ℝ (M u) v = inner ℝ (M u') v := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hM u, hM u', hu, hv] with x hleft hright hueq hvzero
  by_cases hx : x ∈ S
  · rw [hleft, hright, hueq hx]
  · rw [hvzero hx, inner_zero_right, inner_zero_right]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem schwartz_toLp_zero_off_support (g : 𝓢(E, F)) :
    ∀ᵐ x ∂(volume : Measure E), x ∉ tsupport g → g.toLp 2 volume x = 0 := by
  filter_upwards [g.coeFn_toLp 2 volume] with x hx hs
  rw [hx, image_eq_zero_of_notMem_tsupport hs]

variable [CompleteSpace F]

theorem vectorSobolevL2Embedding_cutoff_eq_on (g : 𝓢(E, ℂ)) {S : Set E}
    (hg : ∀ x ∈ S, g x = 1) (u : Lp F 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ S →
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g u) x =
        AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u x := by
  rw [VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding]
  filter_upwards [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply_coe g (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)] with x hx hS
  rw [hx, hg x hS, one_smul]

end

end OAI.Analysis.HodgeTheory.Decomposition.PairLocality.Constructions
