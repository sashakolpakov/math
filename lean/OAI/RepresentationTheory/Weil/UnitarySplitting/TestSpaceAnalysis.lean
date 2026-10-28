import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Test Space Analysis -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis.Construction

noncomputable section

section

/-! Analytic properties of the concrete Bruhat space used by UnitarySplitting.
These elementary proofs keep UnitarySplitting independent of concurrent LocalWeil proof development. -/

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction

open _root_.MeasureTheory
open scoped ENNReal SchwartzMap

theorem localField_proper
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : ProperSpace k := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (h hd).elim
  · exact ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k

theorem localField_secondCountable
    (k : Type) [NormedField k] [LocallyCompactSpace k]
    (h : ¬ DiscreteTopology k) : SecondCountableTopology k := by
  let : ProperSpace k := localField_proper k h
  infer_instance

theorem schwartzBruhat_continuous
    {k : Type} [NormedField k] {n : ℕ}
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Continuous f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous
      · exact φ.continuous.comp e.symm.continuous
  | zero => exact continuous_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact continuous_const.smul hf

theorem schwartzBruhat_memLp
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : MemLp f p μ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨d, e, φ, rfl⟩
      · exact hf.1.continuous.memLp_of_hasCompactSupport hf.2
      · let : (μ.map e.symm).IsAddHaarMeasure := e.symm.isAddHaarMeasure_map μ
        exact (φ.memLp p (μ.map e.symm)).comp_of_map
          e.symm.continuous.measurable.aemeasurable
  | zero => exact MemLp.zero
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

theorem schwartzBruhat_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Integrable f.val μ :=
  memLp_one_iff_integrable.mp (schwartzBruhat_memLp μ 1 f.property)

theorem schwartzBruhat_norm_sq_integrable
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    [SecondCountableTopology k]
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) : Integrable (fun x => ‖f.val x‖ ^ 2) μ :=
  (schwartzBruhat_memLp μ 2 f.property).integrable_norm_pow (by decide)

end

/-! A global bound for every concrete Bruhat test function. -/

open OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction

theorem schwartzBruhat_norm_bound
    {F : Type} [NormedField F] {d : ℕ}
    {f : Local.FunctionsMetaplectic.Construction.Position F d → ℂ} (hf : f ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat F d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      rcases hf with hf | ⟨n, e, φ, rfl⟩
      · obtain ⟨C, hC, hb⟩ := (hf.2.isCompact_range hf.1.continuous).isBounded.exists_pos_norm_le
        exact ⟨C, hC.le, fun x => hb (f x) ⟨x, rfl⟩⟩
      · refine ⟨‖φ.toBoundedContinuousFunction‖, norm_nonneg _, fun x => ?_⟩
        exact φ.toBoundedContinuousFunction.norm_coe_le_norm (e.symm x)
  | zero => exact ⟨0, le_rfl, fun _ => by simp⟩
  | add f g _ _ hf hg =>
      obtain ⟨C, hC, hb⟩ := hf
      obtain ⟨D, hD, hd⟩ := hg
      exact ⟨C + D, add_nonneg hC hD, fun x => (norm_add_le _ _).trans (add_le_add (hb x) (hd x))⟩
  | smul a f _ hf =>
      obtain ⟨C, hC, hb⟩ := hf
      refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, fun x => ?_⟩
      change ‖a • f x‖ ≤ ‖a‖ * C
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TestSpaceAnalysis.Construction
