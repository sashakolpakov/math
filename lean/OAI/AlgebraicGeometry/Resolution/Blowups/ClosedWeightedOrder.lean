import OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.ClosedOrder
import OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialCoefficientOrder

/-! # Closed Weighted Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder.Construction

noncomputable section

/-! Weighted coefficient order at closed points of actual hypersurface quotients. -/

theorem closedPoint_local_order_iff {R : Type*} [CommRing R]
    (J q : Ideal R) [q.IsMaximal] (n : ℕ) :
    J.map (algebraMap R (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n ↔ J ≤ q ^ n := by
  rw [Ideal.map_le_iff_le_comap]
  change J ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n).under R ↔ _
  rw [IsLocalization.AtPrime.under_maximalIdeal_pow q (Localization.AtPrime q) n]

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

include σ K in
/-- At every closed point, without a chosen coordinate value, the weighted
ideal represents exactly the full list of coefficient controls. -/
theorem etale_closedPoint_weighted_order_iff (q : Ideal S) [q.IsMaximal]
    (b : ℕ) (J : Fin b → Ideal S) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ q ^ b.factorial ↔ ∀ j, J j ≤ q ^ (b - j.val) := by
  obtain ⟨x, hx⟩ := Blowups.Etale.ClosedOrder.Construction.finiteType_maximalIdeal_liesOver_polynomialPoint (K := K) (σ := σ) q
  let : q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x) := hx
  simpa only [closedPoint_local_order_iff] using
    WeightedCoefficientIdeal.Construction.etale_weightedCoefficientIdeal_local_order_iff x q b J

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [Algebra ℚ A]

/-- The weighted differential coefficient ideal on the actual quotient hypersurface. -/
def weightedDifferentialCoefficientIdeal (D : Derivation k A A) (z : A) (J : Ideal A) (b : ℕ) :
    Ideal (A ⧸ Ideal.span {z}) :=
  WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z J j.val)

include σ K in
/-- At a closed point on an étale coordinate hypersurface, a single ideal
on that hypersurface detects the ambient order exactly. -/
theorem closedPoint_order_iff_weightedDifferentialCoefficients
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    [Algebra (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    (J q : Ideal A) [q.IsMaximal] (hzq : z ∈ q) (b : ℕ) :
    J ≤ q ^ b ↔ weightedDifferentialCoefficientIdeal D z J b ≤
      q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  let N := q.map (Ideal.Quotient.mk (Ideal.span {z}))
  let : N.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
    Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact (Ideal.span_singleton_le_iff_mem q).mpr hzq)
  rw [DifferentialCoefficientOrder.Construction.ideal_order_iff_differentialCoefficientIdeals D z hz J q hzq b]
  change (∀ j < b, DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z J j ≤ N ^ (b - j)) ↔
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b (fun j => DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z J j.val) ≤ N ^ b.factorial
  rw [etale_closedPoint_weighted_order_iff (σ := σ) (K := K) N]
  exact ⟨fun h j => h j.val j.isLt, fun h j hj => h ⟨j, hj⟩⟩

include σ K in
/-- The same hypersurface reduction with the ambient order expressed in
the local ring, as required by the resolution order locus. -/
theorem closedPoint_local_order_iff_weightedDifferentialCoefficients
    (D : Derivation k A A) (z : A) (hz : D z = 1)
    [Algebra (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    [Algebra.Etale (MvPolynomial σ K) (A ⧸ Ideal.span {z})]
    (J q : Ideal A) [q.IsMaximal] (hzq : z ∈ q) (b : ℕ) :
    J.map (algebraMap A (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b ↔
      weightedDifferentialCoefficientIdeal D z J b ≤
        q.map (Ideal.Quotient.mk (Ideal.span {z})) ^ b.factorial := by
  rw [closedPoint_local_order_iff]
  exact closedPoint_order_iff_weightedDifferentialCoefficients (σ := σ) (K := K) D z hz J q hzq b

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ClosedWeightedOrder.Construction
