import OAI.Analysis.Fourier.SquareFunction.Dyadic.Average
import OAI.Analysis.Fourier.SquareFunction.GoodLambda

/-! The actual good-lambda estimate for finite dyadic averaging families. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

/-- A stopping cube has mean at most the parent/child volume ratio times the
stopping level. No analytic maximal estimate is assumed here. -/
theorem stoppingMean_le_of_parent {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (s : Finset (Set X)) (root : Set X)
    (hQ0 : ∀ Q ∈ s, μ Q ≠ 0) (hQtop : ∀ Q ∈ s, μ Q ≠ ∞)
    {D t : ℝ≥0∞} (hroot : positiveSetMean μ f root ≤ t)
    (hparent : ∀ Q ∈ s, Q ≠ root → ∃ P ∈ s, Q ⊂ P ∧ μ P ≤ D * μ Q)
    {Q : Set X} (hQ : Q ∈ maximalSets (s.filter (fun Q => t < positiveSetMean μ f Q))) :
    positiveSetMean μ f Q ≤ D * t := by
  classical
  have hmax := mem_maximalSets.mp hQ
  obtain ⟨hQs, hQhigh⟩ := Finset.mem_filter.mp hmax.1
  have hQroot : Q ≠ root := by
    intro he
    subst Q
    exact (not_lt_of_ge hroot) hQhigh
  obtain ⟨P, hPs, hQP, hvol⟩ := hparent Q hQs hQroot
  have hPmean : positiveSetMean μ f P ≤ t := by
    by_contra! hP
    have hPQ := hmax.2 (Finset.mem_filter.mpr ⟨hPs, hP⟩) hQP.1
    exact hQP.2 hPQ
  have hbound : positiveSetMean μ f Q * μ Q ≤ (D * t) * μ Q := by
    calc
      _ = ∫⁻ x in Q, ENNReal.ofReal (f x) ∂μ :=
        positiveSetMean_mul_measure μ f Q (hQ0 Q hQs) (hQtop Q hQs)
      _ ≤ ∫⁻ x in P, ENNReal.ofReal (f x) ∂μ := lintegral_mono_set hQP.1
      _ = positiveSetMean μ f P * μ P :=
        (positiveSetMean_mul_measure μ f P (hQ0 P hPs) (hQtop P hPs)).symm
      _ ≤ t * (D * μ Q) := mul_le_mul hPmean hvol bot_le bot_le
      _ = _ := by ac_rfl
  calc
    _ = (positiveSetMean μ f Q * μ Q) * (μ Q)⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel (hQ0 Q hQs) (hQtop Q hQs), mul_one]
    _ ≤ ((D * t) * μ Q) * (μ Q)⁻¹ := mul_le_mul_left hbound _
    _ = D * t := by rw [mul_assoc, ENNReal.mul_inv_cancel (hQ0 Q hQs) (hQtop Q hQs), mul_one]

/-- On each stopping cube, the weak estimate for the oscillation controls the
part where the maximal function is large and the sharp function is small.
The stopping-mean hypothesis is supplied by the dyadic parent-volume ratio. -/
theorem finite_family_good_lambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfn : ∀ x, 0 ≤ f x)
    (s : Finset (Set X)) (hs : IsLaminar s)
    (hm : ∀ Q ∈ s, MeasurableSet Q) (hQ0 : ∀ Q ∈ s, μ Q ≠ 0)
    (hQtop : ∀ Q ∈ s, μ Q ≠ ∞)
    (hmean : ∀ Q ∈ s, positiveSetMean μ f Q ≠ ∞)
    {t β γ : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ∞) (htβ : t ≤ β)
    (hstop : ∀ Q ∈ maximalSets (s.filter (fun Q => t < positiveSetMean μ f Q)),
      positiveSetMean μ f Q + t ≤ β) :
    μ {x | β < familySup s (positiveSetMean μ f) x ∧
      familySup s (setOscillation μ f) x ≤ γ * t} ≤
        γ * μ {x | t < familySup s (positiveSetMean μ f) x} := by
  classical
  let low := s.filter (fun Q => t < positiveSetMean μ f Q)
  let stop := maximalSets low
  let E := {x | β < familySup s (positiveSetMean μ f) x ∧
    familySup s (setOscillation μ f) x ≤ γ * t}
  have hlow : low ⊆ s := Finset.filter_subset _ _
  have hstopS : stop ⊆ s := (maximalSets_subset low).trans hlow
  have hcover : E ⊆ ⋃ Q ∈ stop, E ∩ Q := by
    intro x hx
    have hxlow : x ∈ {x | t < familySup s (positiveSetMean μ f) x} :=
      htβ.trans_lt hx.1
    rw [familySup_superlevel, ← iUnion_maximalSets] at hxlow
    rcases mem_iUnion₂.mp hxlow with ⟨Q, hQ, hxQ⟩
    exact mem_iUnion₂.mpr ⟨Q, hQ, hx, hxQ⟩
  have hlocal (Q : Set X) (hQ : Q ∈ stop) : μ (E ∩ Q) ≤ γ * μ Q := by
    by_cases hE : (E ∩ Q).Nonempty
    · obtain ⟨z, hzE, hzQ⟩ := hE
      let r := s.filter (fun R => R ⊆ Q ∧ β < positiveSetMean μ f R)
      have hrs : r ⊆ s := Finset.filter_subset _ _
      have hQr : E ∩ Q ⊆ ⋃ R ∈ r, R := by
        intro x hx
        have hxhigh : x ∈ {x | β < familySup s (positiveSetMean μ f) x} := hx.1.1
        rw [familySup_superlevel] at hxhigh
        rcases mem_iUnion₂.mp hxhigh with ⟨R, hR, hxR⟩
        obtain ⟨hRs, hRhigh⟩ := Finset.mem_filter.mp hR
        have hRlow : R ∈ low := Finset.mem_filter.mpr ⟨hRs, htβ.trans_lt hRhigh⟩
        have hRQ : R ⊆ Q := by
          rcases hs R hRs Q (hstopS hQ) with h | h | h
          · exact h
          · exact (mem_maximalSets.mp hQ).2 hRlow h
          · exact (Set.disjoint_left.mp h hxR hx.2).elim
        exact mem_iUnion₂.mpr ⟨R, Finset.mem_filter.mpr ⟨hRs, hRQ, hRhigh⟩, hxR⟩
      have hweak : t * μ (⋃ R ∈ r, R) ≤
          ∫⁻ x in Q, ‖f x - (positiveSetMean μ f Q).toReal‖ₑ ∂μ :=
        laminar_mean_gap_weak μ f hfn (hs.mono hrs)
          (fun R hR => hm R (hrs hR)) (fun R hR => hQ0 R (hrs hR))
          (fun R hR => hQtop R (hrs hR))
          (fun R hR => (Finset.mem_filter.mp hR).2.1) (hmean Q (hstopS hQ))
          (fun R hR => (hstop Q hQ).trans (Finset.mem_filter.mp hR).2.2.le)
      have hsharp : setOscillation μ f Q ≤ γ * t :=
        (le_familySup_of_mem (hstopS hQ) hzQ).trans hzE.2
      have hbound : t * μ (E ∩ Q) ≤ t * (γ * μ Q) := by
        calc
          _ ≤ t * μ (⋃ R ∈ r, R) := mul_le_mul_right (measure_mono hQr) _
          _ ≤ _ := hweak
          _ = setOscillation μ f Q * μ Q :=
            (setOscillation_mul_measure μ f Q (hQ0 Q (hstopS hQ)) (hQtop Q (hstopS hQ))).symm
          _ ≤ (γ * t) * μ Q := mul_le_mul_left hsharp _
          _ = _ := by ac_rfl
      calc
        μ (E ∩ Q) = t⁻¹ * (t * μ (E ∩ Q)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
        _ ≤ t⁻¹ * (t * (γ * μ Q)) := mul_le_mul_right hbound _
        _ = γ * μ Q := by rw [← mul_assoc, ENNReal.inv_mul_cancel ht0 httop, one_mul]
    · simp [Set.not_nonempty_iff_eq_empty.mp hE]
  have hdisj := maximalSets_pairwiseDisjoint (hs.mono hlow)
  have hmeas (Q : Set X) (hQ : Q ∈ stop) := hm Q (hstopS hQ)
  have hsum : (∑ Q ∈ stop, μ Q) = μ (⋃ Q ∈ stop, Q) := by
    simpa only [id_eq] using (measure_biUnion_finset (μ := μ) hdisj hmeas).symm
  change μ E ≤ _
  calc
    μ E ≤ μ (⋃ Q ∈ stop, E ∩ Q) := measure_mono hcover
    _ ≤ ∑ Q ∈ stop, μ (E ∩ Q) := measure_biUnion_finset_le _ _
    _ ≤ ∑ Q ∈ stop, γ * μ Q := Finset.sum_le_sum hlocal
    _ = γ * μ (⋃ Q ∈ stop, Q) := by rw [← Finset.mul_sum, hsum]
    _ = _ := by rw [iUnion_maximalSets, ← familySup_superlevel]

/-- The good-lambda inequality for an actual finite dyadic-type family, using
only its elementary geometric parent-volume bound. -/
theorem finite_dyadic_good_lambda {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfn : ∀ x, 0 ≤ f x)
    (s : Finset (Set X)) (hs : IsLaminar s)
    (hm : ∀ Q ∈ s, MeasurableSet Q) (hQ0 : ∀ Q ∈ s, μ Q ≠ 0)
    (hQtop : ∀ Q ∈ s, μ Q ≠ ∞)
    (hmean : ∀ Q ∈ s, positiveSetMean μ f Q ≠ ∞)
    (root : Set X) {D t γ : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ∞)
    (hroot : positiveSetMean μ f root ≤ t)
    (hparent : ∀ Q ∈ s, Q ≠ root → ∃ P ∈ s, Q ⊂ P ∧ μ P ≤ D * μ Q) :
    μ {x | D * t + t < familySup s (positiveSetMean μ f) x ∧
      familySup s (setOscillation μ f) x ≤ γ * t} ≤
        γ * μ {x | t < familySup s (positiveSetMean μ f) x} := by
  apply finite_family_good_lambda μ f hfn s hs hm hQ0 hQtop hmean ht0 httop
  · exact (zero_add t).symm.trans_le (add_le_add bot_le le_rfl)
  · intro Q hQ
    exact add_le_add (stoppingMean_le_of_parent μ f s root hQ0 hQtop hroot hparent hQ) le_rfl

theorem finite_dyadic_distribution {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hfn : ∀ x, 0 ≤ f x)
    (s : Finset (Set X)) (hs : IsLaminar s)
    (hm : ∀ Q ∈ s, MeasurableSet Q) (hQ0 : ∀ Q ∈ s, μ Q ≠ 0)
    (hQtop : ∀ Q ∈ s, μ Q ≠ ∞)
    (hmean : ∀ Q ∈ s, positiveSetMean μ f Q ≠ ∞)
    (root : Set X) {D t γ : ℝ≥0∞} (ht0 : t ≠ 0) (httop : t ≠ ∞)
    (hroot : positiveSetMean μ f root ≤ t)
    (hparent : ∀ Q ∈ s, Q ≠ root → ∃ P ∈ s, Q ⊂ P ∧ μ P ≤ D * μ Q) :
    μ {x | D * t + t < familySup s (positiveSetMean μ f) x} ≤
      μ {x | γ * t < familySup s (setOscillation μ f) x} +
        γ * μ {x | t < familySup s (positiveSetMean μ f) x} := by
  have hsub : {x | D * t + t < familySup s (positiveSetMean μ f) x} ⊆
      {x | γ * t < familySup s (setOscillation μ f) x} ∪
        {x | D * t + t < familySup s (positiveSetMean μ f) x ∧
          familySup s (setOscillation μ f) x ≤ γ * t} := by
    intro x hx
    by_cases hh : γ * t < familySup s (setOscillation μ f) x
    · exact Or.inl hh
    · exact Or.inr ⟨hx, le_of_not_gt hh⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  exact add_le_add le_rfl (finite_dyadic_good_lambda μ f hfn s hs hm hQ0 hQtop hmean
    root ht0 httop hroot hparent)

end OAI.Analysis.Fourier.SquareFunction
