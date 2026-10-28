import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Logarithmic Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransform.Construction

noncomputable section

/-! Relative logarithmic differential bounds on actual controlled blowups. -/

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

attribute [local instance] DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem blowupRelativeChartDerivation_logarithmic
    (I : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) :
    DifferentialBlowup.Construction.blowupRelativeChartDerivation k I a D.val ∈ LogarithmicIdeal.Construction.relativeLogarithmicDerivations k
      (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w') := by
  have hD : D.val.restrictScalars ℤ ∈ LogarithmicDerivation.Construction.logarithmicDerivations w := fun i => D.property i
  have h := LogarithmicDerivation.Construction.blowupChartDerivation_logarithmic I a w w' e he ⟨D.val.restrictScalars ℤ, hD⟩
  intro i
  exact h i

theorem firstRelativeLogarithmicDifferentialIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (n : ℕ) (hJ : J ≤ I ^ (n + 1)) :
    ControlledTransform.Construction.blowupControlledTransform I (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J) n a ≤
      LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k
        (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
        (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) := by
  let c := Blowup.Charts.Construction.blowupChartConstants I a a.val
  let T := ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a
  let W : Option ι → Blowup.Charts.Construction.blowupChart I a := fun i => Option.elim i c w'
  let U := LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k W T
  have htotal : (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J).map (Blowup.Charts.Construction.blowupChartConstants I a) ≤
      Ideal.span {c ^ n} * U := by
    rw [Ideal.map_le_iff_le_comap]
    apply sup_le
    · intro p hp
      obtain ⟨q, hq, heq⟩ := DifferentialIdealTransform.Construction.blowup_controlledTransform_section_exists I J a (n + 1) hJ ⟨p, hp⟩
      change Blowup.Charts.Construction.blowupChartConstants I a p ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨c * q, U.mul_mem_left c (LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k W T hq), ?_⟩
      calc
        c ^ n * (c * q) = c ^ (n + 1) * q := by rw [pow_succ c]; exact (mul_assoc (c ^ n) c q).symm
        _ = Blowup.Charts.Construction.blowupChartConstants I a p := heq.symm
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, p⟩, rfl⟩
      obtain ⟨q, hq, heq⟩ := DifferentialIdealTransform.Construction.blowup_controlledTransform_section_exists I J a (n + 1) hJ p
      change Blowup.Charts.Construction.blowupChartConstants I a (D.val p.val) ∈ Ideal.span {c ^ n} * U
      apply Ideal.mem_span_singleton_mul.mpr
      refine ⟨DifferentialBlowup.Construction.blowupRelativeChartDerivation k I a D.val q +
        (n + 1 : ℕ) * Blowup.Charts.Construction.blowupChartConstants I a (D.val a.val) * q, ?_,
        (DifferentialBlowupTransform.Construction.blowupChart_derivative_division I a (D.val.restrictScalars ℤ) n p.val q heq).symm⟩
      apply Ideal.add_mem
      · exact LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k W T
          ⟨DifferentialBlowup.Construction.blowupRelativeChartDerivation k I a D.val,
            blowupRelativeChartDerivation_logarithmic k I a w w' e he D⟩ hq
      · exact U.mul_mem_left _ (LogarithmicIdeal.Construction.le_firstRelativeLogarithmicDifferentialIdeal k W T hq)
  have hcolon := Submodule.colon_mono htotal (Set.Subset.refl (Ideal.span {c ^ n} : Set _))
  have hc : IsRegular (c ^ n) := IsRegular.pow (a := c) n (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  rw [ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular U (c ^ n) hc] at hcolon
  exact hcolon

theorem iteratedRelativeLogarithmicDifferentialIdeal_controlledTransform_le
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (n r : ℕ) (hJ : J ≤ I ^ (n + r)) :
    ControlledTransform.Construction.blowupControlledTransform I (LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J r) n a ≤
      LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
        (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
        (ControlledTransform.Construction.blowupControlledTransform I J (n + r) a) r := by
  induction r generalizing J with
  | zero => simp only [LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal, Nat.add_zero, le_refl]
  | succ r ih =>
    have hJ' : J ≤ I ^ (n + r + 1) := by simpa only [Nat.add_assoc] using hJ
    have hfirst := firstRelativeLogarithmicDifferentialIdeal_controlledTransform_le
      k I J a w w' e he (n + r) hJ'
    have hlog : LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J ≤ I ^ (n + r) :=
      (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal_le_relative k w J).trans
        ((DifferentialBlowup.Construction.firstRelativeDifferentialIdeal_le_ordinary k J).trans
          (DifferentialIdealTransform.Construction.firstDifferentialIdeal_le_pow I J (n + r) hJ'))
    have hind := ih (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J) hlog
    exact hind.trans (by
      simpa only [LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal, Nat.add_assoc] using
        LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_mono k _ r hfirst)

/-- The relative logarithmic unit bound survives the actual controlled
blowup, retaining the old divided boundaries and the new exceptional equation. -/
theorem blowup_preserves_relative_logarithmic_order_bound
    (I J : Ideal R) (a : I) (w : ι → R) (w' : ι → Blowup.Charts.Construction.blowupChart I a) (e : ι → ℕ)
    (he : ∀ i, Blowup.Charts.Construction.blowupChartConstants I a (w i) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ e i * w' i)
    (m : ℕ) (hJ : J ≤ I ^ m)
    (hbound : LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m = ⊤) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k
      (fun i : Option ι => Option.elim i (Blowup.Charts.Construction.blowupChartConstants I a a.val) w')
      (ControlledTransform.Construction.blowupControlledTransform I J m a) m = ⊤ := by
  have h := iteratedRelativeLogarithmicDifferentialIdeal_controlledTransform_le
    k I J a w w' e he 0 m (by simpa only [zero_add] using hJ)
  rw [zero_add, hbound, ResidualCoefficientTransform.Construction.blowupControlledTransform_zero, Ideal.map_top] at h
  exact top_le_iff.mp h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicTransform.Construction
