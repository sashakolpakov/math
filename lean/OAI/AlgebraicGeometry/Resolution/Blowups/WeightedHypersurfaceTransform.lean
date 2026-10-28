import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform

/-! # Weighted Hypersurface Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedHypersurfaceTransform.Construction

noncomputable section

/-! A single transformed weighted ideal detects order on the persistent hypersurface. -/

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Algebra ℚ R]

/-- On the actual hypersurface chart map, the transform of the single weighted
ideal equals the weighted family of the separately transformed coefficients. -/
theorem weightedDifferentialCoefficientIdeal_blowup_colon
    (I J : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (b : ℕ) (hJ : J ≤ I ^ b) :
    ((ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z.val J b).map
        (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ b.factorial}) =
      WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j : Fin b =>
        ((DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j.val).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
          (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
            (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j.val)})) := by
  unfold ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal
  rw [WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal_map]
  apply WeightedCoefficientTransform.Construction.weightedCoefficientIdeal_colon _
    (NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular I a z D ha hz)
  intro j
  rw [HypersurfaceCoefficientTransform.Construction.differentialCoefficientIdeal_blowup_factorization I J a z D ha b j.val
    (Nat.le_of_lt j.isLt) hJ]
  exact Ideal.mul_le_left

variable {σ K : Type u} [Field K] [IsAlgClosed K] [Finite σ]

/-- At every closed point on a chart with étale hypersurface coordinates,
the whole ambient transformed order locus is detected by one controlled
transform on the hypersurface. -/
theorem noetherian_blowup_order_iff_weighted_coefficient_transform
    (I J : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (k : ℕ) (hJ : J ≤ I ^ (k + 1))
    (hzJ : z.val ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J k)
    [Algebra (MvPolynomial σ K) (Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})]
    [Algebra.Etale (MvPolynomial σ K) (Blowup.Charts.Construction.blowupChart I a ⧸ Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})]
    (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) [M.IsMaximal] :
    ControlledTransform.Construction.blowupControlledTransform I J (k + 1) a ≤ M ^ (k + 1) ↔
      ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M ∧
        ((ClosedWeightedOrder.Construction.weightedDifferentialCoefficientIdeal D z.val J (k + 1)).map
          (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
          (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
            (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (k + 1).factorial}) ≤
          M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) ^ (k + 1).factorial := by
  rw [NoetherianCoordinateTransform.Construction.noetherian_blowup_order_locus_iff_coefficient_transforms I J a z D ha hz k hJ hzJ M]
  apply and_congr_right
  intro hzM
  let N := M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))
  let : N.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact (Ideal.span_singleton_le_iff_mem M).mpr hzM)
  rw [weightedDifferentialCoefficientIdeal_blowup_colon I J a z D ha hz (k + 1) hJ]
  rw [ClosedWeightedOrder.Construction.etale_closedPoint_weighted_order_iff (σ := σ) (K := K) N]
  exact ⟨fun h j => h j.val j.isLt, fun h j hj => h ⟨j, hj⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedHypersurfaceTransform.Construction
