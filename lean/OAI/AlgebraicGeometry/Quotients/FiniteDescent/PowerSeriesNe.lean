import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesContinuous
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.HomogeneousLineAt

/-! # Power Series Ne -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesNe.Construction.PowerSeriesRegularDirection

noncomputable section

/-! A nonzero formal power series becomes regular in one variable after a shear. -/

variable {K : Type*} [Field K] [Infinite K] {n : ℕ}

theorem exists_shear_axis_ne_zero (f : MvPowerSeries (Fin (n + 1)) K) (hf : f ≠ 0) :
    ∃ a : Fin n → K, PowerSeriesContinuous.Construction.PowerSeriesAxis.axis (PowerSeriesSubst.Construction.PowerSeriesShear.equiv a f) ≠ 0 := by
  obtain ⟨d, hd⟩ := (MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero f).mp hf
  let P := MvPolynomial.homogeneousComponent d.degree (f.truncTotal (d.degree + 1))
  have hP : P ≠ 0 := by
    intro h
    have hz := congrArg ((fun p => AddMonoidAlgebra.coeff p (d))) h
    rw [MvPolynomial.coeff_homogeneousComponent, ite_eq_left rfl,
      MvPowerSeries.coeff_truncTotal _ (Nat.lt_succ_self _), AddMonoidAlgebra.coeff_zero] at hz
    exact hd hz
  obtain ⟨a, ha⟩ := HomogeneousLineAt.Construction.HomogeneousLine.exists_eval_at_one_ne_zero
    (MvPolynomial.homogeneousComponent_isHomogeneous _ _) hP
  refine ⟨a, ?_⟩
  intro hz
  apply ha
  have hc := congrArg (PowerSeries.coeff d.degree) hz
  rw [PowerSeriesContinuous.Construction.PowerSeriesAxis.axis_shear, PowerSeriesMonomial.Construction.PowerSeriesLine.coeff, map_zero] at hc
  exact hc

theorem exists_shear_reduction_ne_zero (f : MvPowerSeries (Fin (n + 1)) K) (hf : f ≠ 0) :
    ∃ a : Fin n → K,
      (MvPowerSeries.finSuccEquiv K n (PowerSeriesSubst.Construction.PowerSeriesShear.equiv a f)).map
        (IsLocalRing.residue (MvPowerSeries (Fin n) K)) ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_shear_axis_ne_zero f hf
  refine ⟨a, ?_⟩
  intro hz
  apply ha
  apply PowerSeries.ext
  intro m
  have hc := congrArg (PowerSeries.coeff m) hz
  rw [PowerSeries.coeff_map, map_zero] at hc
  have hm := (PowerSeriesIs.Construction.PowerSeriesLocal.mem_maximalIdeal_iff _).mp
    ((IsLocalRing.residue_eq_zero_iff _).mp hc)
  change MvPowerSeries.constantCoeff (PowerSeries.coeff m
    (MvPowerSeries.finSuccEquiv K n (PowerSeriesSubst.Construction.PowerSeriesShear.equiv a f))) = 0
  exact hm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.PowerSeriesNe.Construction.PowerSeriesRegularDirection
