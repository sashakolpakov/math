import OAI.Analysis.HodgeTheory.Decomposition.CommutatorBounds
import OAI.Analysis.HodgeTheory.Decomposition.GraphNorm
import OAI.Analysis.HodgeTheory.Decomposition.Multiplier

/-! # Graph Multiplier -/

namespace OAI.Analysis.HodgeTheory.Decomposition.GraphMultiplier.Constructions

noncomputable section

/-! Smooth real chart cutoffs are bounded in the genuine Hodge graph norm. -/

open scoped _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]

theorem projectiveRealMultiplier_L2_bound (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      ‖Form.Constructions.smoothToProjectiveL2 V n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a)‖ ≤ B * ‖Form.Constructions.smoothToProjectiveL2 V n a‖ := by
  obtain ⟨B, hB⟩ := Multiplier.Constructions.projective_smooth_multiplier_bound V n (fun x => (f x : ℂ))
    (Complex.ofRealCLM.contDiff.contMDiff.comp hf)
  exact ⟨max B 0, le_max_right _ _, fun a =>
    (hB a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))⟩

omit [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace] in
theorem projectiveDCommutator_identity (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf a) =
      ManifoldCommutators.Constructions.projectiveDCommutator V n f hf a + RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) :=
  (sub_add_cancel _ _).symm

theorem projectiveDeltaCommutator_identity (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f)
    (a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1)) :
    AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a) =
      ManifoldCommutators.Constructions.projectiveDeltaCommutator V n f hf a + RealMultiplier.Constructions.projectiveRealMultiplier V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a) :=
  (sub_add_cancel _ _).symm

theorem projectiveRealMultiplier_graph_bound
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ) (f : V.analyticSpace → ℝ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ f) (hs : tsupport f ⊆ e.source) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1),
      ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a)‖ ≤
        B * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ := by
  obtain ⟨M₀, hM₀, hval⟩ := projectiveRealMultiplier_L2_bound V (n + 1) f hf
  obtain ⟨M₁, hM₁, hdval⟩ := projectiveRealMultiplier_L2_bound V (n + 1 + 1) f hf
  obtain ⟨M₂, hM₂, htval⟩ := projectiveRealMultiplier_L2_bound V n f hf
  obtain ⟨C₁, hC₁, hdcomm⟩ := CommutatorBounds.Constructions.projectiveDCommutator_L2_bound V e he (n + 1) f hf hs
  obtain ⟨C₂, hC₂, htcomm⟩ := CommutatorBounds.Constructions.projectiveDeltaCommutator_L2_bound V e he n f hf hs
  refine ⟨M₀ + (C₁ + M₁) + (C₂ + M₂), by positivity, fun a => ?_⟩
  obtain ⟨h₀, h₁, h₂⟩ := GraphNorm.Constructions.projectiveGraphEmbedding_component_bounds V n a
  have hvalue := (hval a).trans (mul_le_mul_of_nonneg_left h₀ hM₀)
  have hd : ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1)
      (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a))‖ ≤
      (C₁ + M₁) * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ := by
    rw [projectiveDCommutator_identity, map_add]
    calc
      _ ≤ ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (ManifoldCommutators.Constructions.projectiveDCommutator V (n + 1) f hf a)‖ +
          ‖Form.Constructions.smoothToProjectiveL2 V (n + 1 + 1) (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1 + 1) f hf (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a))‖ := norm_add_le _ _
      _ ≤ C₁ * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ + M₁ * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ :=
        add_le_add ((hdcomm a).trans (mul_le_mul_of_nonneg_left h₀ hC₁))
          ((hdval (DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a)).trans (mul_le_mul_of_nonneg_left h₁ hM₁))
      _ = _ := (add_mul _ _ _).symm
  have ht : ‖Form.Constructions.smoothToProjectiveL2 V n
      (AdjointAlgebra.Constructions.projectiveCodifferential V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a))‖ ≤
      (C₂ + M₂) * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ := by
    rw [projectiveDeltaCommutator_identity, map_add]
    calc
      _ ≤ ‖Form.Constructions.smoothToProjectiveL2 V n (ManifoldCommutators.Constructions.projectiveDeltaCommutator V n f hf a)‖ +
          ‖Form.Constructions.smoothToProjectiveL2 V n (RealMultiplier.Constructions.projectiveRealMultiplier V n f hf (AdjointAlgebra.Constructions.projectiveCodifferential V n a))‖ := norm_add_le _ _
      _ ≤ C₂ * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ + M₂ * ‖EnergyDomain.Constructions.projectiveGraphEmbedding V n a‖ :=
        add_le_add ((htcomm a).trans (mul_le_mul_of_nonneg_left h₀ hC₂))
          ((htval (AdjointAlgebra.Constructions.projectiveCodifferential V n a)).trans (mul_le_mul_of_nonneg_left h₂ hM₂))
      _ = _ := (add_mul _ _ _).symm
  exact (GraphNorm.Constructions.projectiveGraphEmbedding_norm_le_sum V n (RealMultiplier.Constructions.projectiveRealMultiplier V (n + 1) f hf a)).trans
    ((add_le_add (add_le_add hvalue hd) ht).trans_eq (by ring))

end

end OAI.Analysis.HodgeTheory.Decomposition.GraphMultiplier.Constructions
