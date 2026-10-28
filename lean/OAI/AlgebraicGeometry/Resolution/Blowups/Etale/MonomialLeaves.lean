import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialVerification
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialStep
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound

/-! # Monomial Leaves -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialLeaves.Construction

noncomputable section

/-! Leaf order bounds persist for monomial ideals on arbitrary étale ambient coordinate neighborhoods. -/

open _root_.MvPolynomial

universe u

variable {σ K S : Type u} [Fintype σ] [DecidableEq σ]
  [Field K] [CharZero K] [CommRing S]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

omit [DecidableEq σ] in
/-- The differential ideal of an extended monomial becomes the unit ideal
within the same exponent bound, even if the ambient étale ring is disconnected. -/
theorem etaleCoordinateMonomial_differential_bound (a : σ → ℕ) :
    DifferentialIdealTransform.Construction.iteratedDifferentialIdeal
      ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) a}).map (algebraMap (MvPolynomial σ K) S))
      (∑ j, a j) = ⊤ := by
  let J : Ideal (MvPolynomial σ K) := Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial a}
  have hd : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J (∑ j, a j) = ⊤ :=
    DifferentialOrderLocus.Construction.iteratedDifferentialIdeal_eq_top_of_degree_bound (∑ j, a j) J (MonomialBlowupChart.Construction.coordinateMonomial a)
      (MonomialVerification.Construction.coordinateMonomial_totalDegree_le a) (Ideal.mem_span_singleton_self _) (MonomialVerification.Construction.coordinateMonomial_ne_zero a)
  apply top_le_iff.mp
  have h := Derivation.Construction.iteratedDifferentialIdeal_map_le_of_etale (S := S) J (∑ j, a j)
  rwa [hd, Ideal.map_top] at h

omit [DecidableEq σ] in
/-- Every prime of an étale monomial leaf has order below the
control. No integrality or nonzero-ideal assumption on the ambient ring is needed. -/
theorem etaleCoordinateMonomial_leaf_order (a : σ → ℕ) (b : ℕ) (hb : (∑ j, a j) < b)
    (q : Ideal S) [q.IsPrime] :
    ¬ ((Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) a}).map (algebraMap (MvPolynomial σ K) S)).map
        (algebraMap S (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  intro h
  let J := (Ideal.span {MonomialBlowupChart.Construction.coordinateMonomial (R := K) a}).map (algebraMap (MvPolynomial σ K) S)
  exact DifferentialLocalBound.Construction.local_order_lt_of_differential_top J (∑ j, a j)
    (etaleCoordinateMonomial_differential_bound a) q
    (h.trans (Ideal.pow_le_pow_right (by omega)))

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialLeaves.Construction
