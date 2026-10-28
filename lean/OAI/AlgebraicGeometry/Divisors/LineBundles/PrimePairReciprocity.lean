import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineFunctionUnits

/-! # Prime Pair Reciprocity -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.PrimePairReciprocity.BundleCycles

noncomputable section

/-!
# LineBundleCycles: residue reciprocity for prime elements, including a shared component

Distinct prime elements have disjoint divisor components, so proper
reciprocity applies. If one divides the other, primality makes the
remaining factor a unit; bilinearity, the diagonal identity, and the
actual unit case prove vanishing on that shared component as well.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
variable [IsLocalRing R] [IsIntegrallyClosed R]

theorem affinePrimePairResidueBoundary_zero (p q : R) (hp : Prime p) (hq : Prime q)
    (hdim : ringKrullDim R = 2) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle (Spec (CommRingCat.of R)) (Affine.ProperReciprocity.BundleCycles.affineNormal_stalk_integrallyClosed R)
      (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R p hp.ne_zero) (Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R q hq.ne_zero) = 0 := by
  by_cases hdvd : q ∣ p
  · obtain ⟨r, hr⟩ := hdvd
    have hru : IsUnit r := (hp.irreducible.isUnit_or_isUnit hr).resolve_left hq.not_isUnit
    have he : Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R p hp.ne_zero =
        Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R q hq.ne_zero * Affine.ProperReciprocity.BundleCycles.affineFunctionUnit R r hru.ne_zero := by
      subst p
      exact AffineFunctionUnits.BundleCycles.affineFunctionUnit_mul R q r hq.ne_zero hru.ne_zero
    rw [he, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_mul_left, ResidueBoundaryAddition.BundleCycles.normalResidueBoundaryCycle_self,
      AffineFunctionUnits.BundleCycles.affineResidueBoundary_unit_left R r hru, zero_add]
  · apply AffineFunctionUnits.BundleCycles.affineDisjointResidueBoundary_zero R p q hp.ne_zero hq.ne_zero hdim
    intro P hP
    let : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hP
    subst P
    exact fun h => hdvd (Ideal.mem_span_singleton.mp h)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.PrimePairReciprocity.BundleCycles
