import OAI.RepresentationTheory.Weil.UnitarySplitting.NormQuadraticIntegrals

/-! # Character Cutoffs -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterCutoffs.Construction

noncomputable section

/-! Vanishing additive-character integrals on translation-invariant cutoffs. -/

open _root_.MeasureTheory _root_.Topology

theorem character_cutoff_integral_zero
    {A : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (μ : Measure A) [μ.IsAddLeftInvariant] (ψ : AddChar A ℂ)
    (S : Set A) (t : A) (htranslate : ∀ x, t + x ∈ S ↔ x ∈ S) (ht : ψ t ≠ 1) :
    (∫ x, S.indicator (fun x => ψ x) x ∂μ) = 0 := by
  classical
  have heq (x : A) :
      S.indicator (fun x => ψ x) (t + x) = ψ t * S.indicator (fun x => ψ x) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem ((htranslate x).mpr hx), Set.indicator_of_mem hx, ψ.map_add_eq_mul]
    · rw [Set.indicator_of_notMem (fun h => hx ((htranslate x).mp h)),
        Set.indicator_of_notMem hx, mul_zero]
  have hh := integral_add_left_eq_self (μ := μ) (S.indicator (fun x => ψ x)) t
  simp_rw [heq, integral_const_mul] at hh
  by_contra hi
  apply ht
  apply mul_right_cancel₀ hi
  simpa only [one_mul] using hh

theorem ultra_closedBall_translate
    {F : Type} [NormedField F] [IsUltrametricDist F] (r : ℝ) (t : F) (ht : ‖t‖ ≤ r) :
    ∀ x : F, t + x ∈ Metric.closedBall 0 r ↔ x ∈ Metric.closedBall 0 r := by
  intro x
  simp only [Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro hx
    calc
      ‖x‖ = ‖-t + (t + x)‖ := by congr 1; abel
      _ ≤ max ‖-t‖ ‖t + x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ r := max_le (by simpa using ht) hx
  · intro hx
    exact (IsUltrametricDist.norm_add_le_max t x).trans (max_le ht hx)

theorem ultra_character_closedBall_integral_zero
    {F : Type} [NormedField F] [IsUltrametricDist F]
    [MeasurableSpace F] [BorelSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (ψ : AddChar F ℂ)
    (t : F) (ht : ψ t ≠ 1) (r : ℝ) (hr : ‖t‖ ≤ r) :
    (∫ x, (Metric.closedBall (0 : F) r).indicator (fun x => ψ x) x ∂μ) = 0 :=
  character_cutoff_integral_zero μ ψ _ t (ultra_closedBall_translate r t hr) ht

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterCutoffs.Construction
