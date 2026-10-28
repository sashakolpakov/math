import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleLocalOrder

/-! # Prime Order Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality.Construction

noncomputable section

/-! Exact local-order comparison for affine ideals at arbitrary étale-corresponding primes. -/

variable {R V : Type*} [CommRing R] [CommRing V]

/-- Extending an affine ideal across an étale map preserves every local-order
threshold at corresponding prime points, including non-closed points. -/
theorem etale_map_prime_order_iff (f : R →+* V) (hf : f.Etale)
    (J q : Ideal R) (Q : Ideal V) [q.IsPrime] [Q.IsPrime] (hQ : q = Q.comap f) (b : ℕ) :
    (J.map f).map (algebraMap V (Localization.AtPrime Q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ b ↔
      J.map (algebraMap R (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  have he : (J.map (algebraMap R (Localization.AtPrime q))).map
      (Localization.localRingHom q Q f hQ) =
      (J.map f).map (algebraMap V (Localization.AtPrime Q)) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro x
    exact Localization.localRingHom_to_map q Q f hQ x
  rw [← he]
  exact Pointed.EtaleLocalOrder.Construction.pointed_etale_local_ideal_order_iff f hf q Q hQ
    (J.map (algebraMap R (Localization.AtPrime q))) b

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality.Construction
