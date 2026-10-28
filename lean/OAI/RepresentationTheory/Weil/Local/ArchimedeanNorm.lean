import OAI.RepresentationTheory.Weil.Local.Coordinates

/-! # Archimedean Norm -/

namespace OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm.Construction

noncomputable section

/-! The chosen norm at an archimedean place is a positive power of the ordinary absolute value. -/

theorem realEmbedding_norm_power
    (k : Type) [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ x : ℝ, ‖Coordinates.Construction.realEmbeddingOfUnbounded k h x‖ = |x| ^ s := by
  have hh : ¬ ∀ n : ℕ, Coordinates.Construction.rationalNorm k n ≤ 1 := by simpa [Coordinates.Construction.rationalNorm] using h
  have he := Rat.AbsoluteValue.equiv_real_of_unbounded hh
  obtain ⟨s, hs, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he.symm
  have hp (q : ℚ) : ‖(q : k)‖ = ‖q‖ ^ s := by
    have hq := congrFun heq q
    simpa [Coordinates.Construction.rationalNorm, Rat.AbsoluteValue.real_eq_abs, ← Real.norm_eq_abs,
      Rat.norm_cast_real] using hq.symm
  have hc : Continuous (fun x : ℝ => ‖x‖ ^ s) := continuous_norm.rpow_const (fun _ => Or.inr hs.le)
  have H := Rat.denseRange_cast.equalizer
    (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h).norm hc
    (show (fun x : ℝ => ‖Coordinates.Construction.realEmbeddingOfUnbounded k h x‖) ∘ (Rat.castHom ℝ) =
      (fun x : ℝ => ‖x‖ ^ s) ∘ (Rat.castHom ℝ) from by
        funext q
        change ‖Coordinates.Construction.realEmbeddingOfUnbounded k h (q : ℝ)‖ = ‖(q : ℝ)‖ ^ s
        rw [map_ratCast, Rat.norm_cast_real]
        exact hp q)
  have h2 : ‖(2 : k)‖ ≤ (2 : ℝ) := by
    calc
      _ = ‖(1 : k) + 1‖ := by congr 1; norm_num
      _ ≤ ‖(1 : k)‖ + ‖(1 : k)‖ := norm_add_le _ _
      _ = 2 := by norm_num
  have hp2 : ‖(2 : k)‖ = (2 : ℝ) ^ s := by
    simpa only [map_ofNat, Real.norm_ofNat] using congrFun H 2
  refine ⟨s, hs, ?_, fun x => ?_⟩
  · apply (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp
    rw [Real.rpow_one, ← hp2]
    exact h2
  · simpa only [Real.norm_eq_abs] using congrFun H x

theorem continuous_real_embedding_unique
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℝ →+* k) (he : Continuous e) :
    e = Coordinates.Construction.realEmbeddingOfUnbounded k h := by
  apply RingHom.ext
  have H := Rat.denseRange_cast.equalizer he (Coordinates.Construction.realEmbeddingOfUnbounded_continuous k h)
    (show e ∘ (Rat.castHom ℝ) = Coordinates.Construction.realEmbeddingOfUnbounded k h ∘ (Rat.castHom ℝ) from by
      funext q
      change e (q : ℝ) = Coordinates.Construction.realEmbeddingOfUnbounded k h (q : ℝ)
      rw [map_ratCast, map_ratCast])
  exact congrFun H

theorem continuous_real_embedding_norm_power
    {k : Type} [NormedField k] [CompleteSpace k] [CharZero k]
    (h : ¬ ∀ n : ℕ, ‖(n : k)‖ ≤ 1) (e : ℝ →+* k) (he : Continuous e) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ ∀ x : ℝ, ‖e x‖ = |x| ^ s := by
  rw [continuous_real_embedding_unique h e he]
  exact realEmbedding_norm_power k h

end

end OAI.RepresentationTheory.Weil.Local.ArchimedeanNorm.Construction
