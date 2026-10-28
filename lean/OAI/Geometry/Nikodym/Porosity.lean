import Mathlib.MeasureTheory.Covering.DensityTheorem

open Set Filter Metric _root_.MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OAI.Geometry.Nikodym

variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
  [SecondCountableTopology X] [BorelSpace X]
  (μ : Measure X) [IsUnifLocDoublingMeasure μ] [IsLocallyFiniteMeasure μ]

/-- A density point cannot have a uniformly nearby empty ball at every
sufficiently small scale. The centers need not equal the density point. -/
theorem measure_eq_zero_of_small_holes {S : Set X} (hS : MeasurableSet S) (K : ℝ)
    (hhole : ∀ x ∈ S, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ y, dist x y ≤ K*r ∧ Disjoint S (closedBall y r)) : μ S = 0 := by
  classical
  have hfalse : ∀ᵐ x ∂μ.restrict S, False := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S K,
      ae_restrict_mem hS] with x hx hxS
    let w : ℝ → X := fun r => if h : ∃ y, dist x y ≤ K*r ∧ Disjoint S (closedBall y r)
      then Classical.choose h else x
    have hw : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        dist x (w r) ≤ K*r ∧ Disjoint S (closedBall (w r) r) := by
      filter_upwards [hhole x hxS] with r hr
      dsimp only [w]
      rw [dite_eq_left hr]
      exact Classical.choose_spec hr
    have ht := hx w id tendsto_id (hw.mono fun r hr => hr.1)
    have he : (fun r => μ (S ∩ closedBall (w r) r) / μ (closedBall (w r) r))
        =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hw] with r hr
      rw [hr.2.inter_eq,measure_empty,ENNReal.zero_div]
    have h01 : (0 : ℝ≥0∞)=1 :=
      tendsto_nhds_unique tendsto_const_nhds (ht.congr' he)
    exact zero_ne_one h01
  simpa only [ae_iff,not_false_eq_true,Set.ofPred_true,Measure.restrict_apply_univ] using hfalse

/-- The hole-size ratio may depend on the point, as long as it stays fixed
while the radius tends to zero. -/
theorem measure_eq_zero_of_pointwise_small_holes {S : Set X} (hS : MeasurableSet S)
    (hhole : ∀ x ∈ S, ∃ K : ℕ, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∃ y, dist x y ≤ (K:ℝ)*r ∧ Disjoint S (closedBall y r)) : μ S = 0 := by
  classical
  have hd : ∀ᵐ x ∂μ.restrict S, ∀ K : ℕ,
      ∀ (w : ℝ → X),
        (∀ᶠ r in 𝓝[>] (0:ℝ),x ∈ closedBall (w r) ((K:ℝ)*r)) →
        Tendsto (fun r => μ (S ∩ closedBall (w r) r) / μ (closedBall (w r) r))
          (𝓝[>] (0:ℝ)) (𝓝 1) := by
    apply ae_all_iff.mpr
    intro K
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div μ S K]
      with x hx
    intro w hw
    exact hx w id tendsto_id hw
  have hfalse : ∀ᵐ x ∂μ.restrict S, False := by
    filter_upwards [hd,ae_restrict_mem hS] with x hx hxS
    obtain ⟨K,hK⟩ := hhole x hxS
    let w : ℝ → X := fun r => if h : ∃ y, dist x y ≤ (K:ℝ)*r ∧ Disjoint S (closedBall y r)
      then Classical.choose h else x
    have hw : ∀ᶠ r in 𝓝[>] (0 : ℝ),
        dist x (w r) ≤ (K:ℝ)*r ∧ Disjoint S (closedBall (w r) r) := by
      filter_upwards [hK] with r hr
      dsimp only [w]
      rw [dite_eq_left hr]
      exact Classical.choose_spec hr
    have ht := hx K w (hw.mono fun r hr => hr.1)
    have he : (fun r => μ (S ∩ closedBall (w r) r) / μ (closedBall (w r) r))
        =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (0 : ℝ≥0∞) := by
      filter_upwards [hw] with r hr
      rw [hr.2.inter_eq,measure_empty,ENNReal.zero_div]
    exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds (ht.congr' he))
  simpa only [ae_iff,not_false_eq_true,Set.ofPred_true,Measure.restrict_apply_univ] using hfalse

end OAI.Geometry.Nikodym
