import OAI.AlgebraicGeometry.Resolution.Blowups.MarkedIdealIntersection
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.CenterPermissibility
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualCoefficientTransform

/-! # Companion Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.CompanionCenter.Construction

noncomputable section

/-! Companion centers for a residual ideal whose order is below the total control. -/

section

variable {R : Type*} [CommRing R]

/-- Combine residual control `m` with the needed exceptional control `b-m`. -/
def companionIdeal (J M : Ideal R) (m b : ℕ) : Ideal R :=
  MarkedIdealIntersection.Construction.markedIdealIntersection J M m (b - m)

end

universe u

variable {σ K S : Type u} [Field K] [IsAlgClosed K] [CharZero K] [CommRing S]
  [Finite σ] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- The pointwise criterion also includes control zero. -/
theorem etale_coordinate_center_order_iff (C : Finset σ) (J : Ideal S) (b : ℕ) :
    J ≤ ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) ^ b ↔
      ∀ (q : Ideal S) [q.IsMaximal],
        (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S) ≤ q →
          J ≤ q ^ b := by
  cases b with
  | zero => simp only [pow_zero, Ideal.one_eq_top, le_top, implies_true]
  | succ b =>
    simpa only [ClosedWeightedOrder.Construction.closedPoint_local_order_iff] using
      Coordinate.CenterPermissibility.Construction.etale_coordinate_center_permissible_iff_closedPoint_order C J b

/-- Along every actual smooth coordinate center, the common marked ideal
has exactly the two original permissibility conditions. -/
theorem etale_coordinate_center_markedIntersection_iff
    (C : Finset σ) (J L : Ideal S) (b c : ℕ) (hb : 0 < b) (hc : 0 < c) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
    MarkedIdealIntersection.Construction.markedIdealIntersection J L b c ≤ I ^ (b * c) ↔ J ≤ I ^ b ∧ L ≤ I ^ c := by
  let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
  constructor
  · intro h
    have hp : ∀ (q : Ideal S) [q.IsMaximal], I ≤ q → J ≤ q ^ b ∧ L ≤ q ^ c := by
      intro q _ hq
      exact (MarkedIdealIntersection.Construction.etale_closedPoint_markedIdealIntersection_order_iff (σ := σ) (K := K) J L q b c hb hc).mp
        (h.trans (pow_le_pow_left' hq (b * c)))
    exact ⟨(etale_coordinate_center_order_iff C J b).mpr (fun q _ hq => (hp q hq).1),
      (etale_coordinate_center_order_iff C L c).mpr (fun q _ hq => (hp q hq).2)⟩
  · rintro ⟨hJ, hL⟩
    exact MarkedIdealIntersection.Construction.markedIdealIntersection_permissible I J L b c hJ hL

/-- A companion center supplies both the residual and exceptional controls,
and consequently the actual total-product control. -/
theorem etale_companion_center_permissible (C : Finset σ) (J M : Ideal S) (m b : ℕ)
    (hm : 0 < m) (hmb : m < b)
    (hcomp : companionIdeal J M m b ≤
      ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) ^ (m * (b - m))) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
    J ≤ I ^ m ∧ M ≤ I ^ (b - m) ∧ M * J ≤ I ^ b := by
  obtain ⟨hJ, hM⟩ := (etale_coordinate_center_markedIntersection_iff C J M m (b - m) hm
    (by omega)).mp hcomp
  exact ⟨hJ, hM, ResidualCoefficientTransform.Construction.product_center_permissible _ M J (b - m) m b (by omega) hM hJ⟩

/-- At a companion center there is no unassigned exceptional exponent:
the total transform is the product of the separately controlled factors. -/
theorem etale_companion_blowup_product (C : Finset σ) (J M : Ideal S) (m b : ℕ)
    (hm : 0 < m) (hmb : m < b)
    (hcomp : companionIdeal J M m b ≤
      ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) ^ (m * (b - m)))
    (a : (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)) :
    let I := (SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map (algebraMap (MvPolynomial σ K) S)
    ControlledTransform.Construction.blowupControlledTransform I (M * J) b a =
      ControlledTransform.Construction.blowupControlledTransform I M (b - m) a * ControlledTransform.Construction.blowupControlledTransform I J m a := by
  obtain ⟨hJ, hM, _⟩ := etale_companion_center_permissible C J M m b hm hmb hcomp
  have he := ResidualCoefficientTransform.Construction.blowup_product_controlledTransform _ M J a (b - m) m b (by omega) hM hJ
  rw [Nat.sub_add_cancel (Nat.le_of_lt hmb), Nat.sub_self,
    pow_zero (Blowup.Charts.Construction.blowupChartConstants _ a a.val), Ideal.span_singleton_one, Ideal.top_mul] at he
  exact he

end

end OAI.AlgebraicGeometry.Resolution.Blowups.CompanionCenter.Construction
