import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitBlowup

/-! # Idempotent Quotient Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientTransform.Construction

noncomputable section

/-! Termination on the chart of an idempotent lifted from the hypersurface quotient. -/

universe u

variable {R : Type u} [CommRing R]

private theorem exceptional_eq_one_of_relation {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (q : B →+* C)
    (a z : A) (t : B) (hc : IsRegular (f a)) (hct : f a * t = f z)
    (ht : q t = 0) (hrel : a * (1 - a) ∈ Ideal.span {z}) : q (f a) = 1 := by
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hrel
  have hcancel : 1 - f a = t * f v := by
    apply hc.left
    change f a * (1 - f a) = f a * (t * f v)
    rw [← mul_assoc, hct, ← map_mul, ← hv, map_mul, map_sub, map_one]
  have h := congrArg q hcancel
  rw [map_sub, map_one, map_mul, ht, zero_mul] at h
  exact (sub_eq_zero.mp h).symm

/-- After dividing the relation expressing quotient idempotence by the
regular exceptional parameter, that parameter becomes one on the transformed hypersurface. -/
theorem idempotent_quotient_chart_exceptional_eq_one (I : Ideal R) (a z : I)
    (hrel : a.val * (1 - a.val) ∈ Ideal.span {z.val}) :
    Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}) (Blowup.Charts.Construction.blowupChartConstants I a a.val) = 1 := by
  exact exceptional_eq_one_of_relation (A := R) (B := Blowup.Charts.Construction.blowupChart I a)
    (C := Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
    (Blowup.Charts.Construction.blowupChartConstants I a) (Ideal.Quotient.mk _) a.val z.val (ExceptionalIdeal.Construction.blowupChartRatio I a z)
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a) (ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a z)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)) hrel

variable (k : Type u) [CommRing k] [Algebra k R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- If the center is the intrinsic tangent ideal, the idempotent chart
is terminal by its exact coefficient transform. -/
theorem idempotent_quotient_chart_differential_unit
    (I J : Ideal R) (a z : I) (n : ℕ) (hJ : J ≤ I ^ (n + 1))
    (hz : z.val ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hrel : a.val * (1 - a.val) ∈ Ideal.span {z.val})
    (hC : I.map (Ideal.Quotient.mk (Ideal.span {z.val})) =
      Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z.val J (n + 1)) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) a) n = ⊤ := by
  let C := I.map (Ideal.Quotient.mk (Ideal.span {z.val}))
  have he := idempotent_quotient_chart_exceptional_eq_one I a z hrel
  have hunit : C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) = ⊤ := by
    apply Ideal.eq_top_of_isUnit_mem _
      (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ a.property))
    change IsUnit (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val))
    rw [he]
    exact isUnit_one
  apply Coefficient.UnitBlowup.Construction.coefficient_unit_transform_clears_ambient k I J a z n hJ hz C hC.le
  · rw [he]
    exact isRegular_one
  · rw [hunit]
    exact Submodule.top_colon

end

end OAI.AlgebraicGeometry.Resolution.Blowups.IdempotentQuotientTransform.Construction
