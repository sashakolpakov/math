import OAI.RepresentationTheory.Weil.Local.CompactCharacter

/-! # Nonarchimedean Inversion -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanInversion.Construction

noncomputable section

/-! Compact frequency domains adapted to nonarchimedean test functions. -/

open _root_.MeasureTheory
open scoped Classical

theorem additiveAnnihilator_small
    {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : k) (ha : ψ a ≠ 1)
    (U : AddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (ε R : ℝ) (hε : 0 < ε)
    (hR : ‖a‖ / ε ≤ R)
    (hU : Metric.closedBall (0 : FunctionsMetaplectic.Construction.Position k n) R ⊆ U) :
    ∀ x ∈ CompactCharacter.Construction.additiveAnnihilator ψ U, ‖x‖ < ε := by
  intro x hx
  apply (pi_norm_lt_iff hε).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hε.trans_le hi)
  let t : FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : t ∈ U := by
    apply hU
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(Pi.single i (a / x i) : FunctionsMetaplectic.Construction.Position k n)‖ ≤ R
    rw [Pi.norm_single, norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hε hi).trans hR
  have hdot : FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  apply ha
  have h := hx t ht
  rwa [hdot] at h

theorem exists_adapted_frequency_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n), IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) ∧
      tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U ∧
      ∀ t ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, f (x + t) = f x := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  have hF := CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μ hf hs
  obtain ⟨R, hR, hbound⟩ := hF.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, heq⟩ := CompactCharacter.Construction.compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hn
  let S : ℝ := max R (‖a‖ / ε) + 1
  have hS : 0 < S := by
    exact lt_trans hR (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) hS
  have hUS : (U : Set (FunctionsMetaplectic.Construction.Position k n)) = Metric.closedBall 0 S := rfl
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUS]
    exact isCompact_closedBall _ _
  · intro x hx
    rw [hUS, Metric.mem_closedBall, dist_zero_right]
    exact (hbound x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  · intro t ht x
    apply heq x t
    apply additiveAnnihilator_small ψ a ha U.toAddSubgroup ε S hε _ _ t ht
    · exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    · exact fun _ hx => hx

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanInversion.Construction
