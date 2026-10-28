import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.FactorNaturality
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Etale Local Order -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleLocalOrder.Construction

noncomputable section

/-! Pointed étale comparisons preserve the order of every local residual ideal. -/

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The induced étale local-ring map carries the source maximal ideal
exactly to the target maximal ideal. -/
theorem pointed_etale_local_maximalIdeal_map (f : R →+* S) (hf : f.Etale)
    (q : Ideal R) (Q : Ideal S) [q.IsPrime] [Q.IsPrime] (hQ : q = Q.comap f) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map (Localization.localRingHom q Q f hQ) =
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Etale R S := hf
  let : Q.LiesOver q := ⟨hQ⟩
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver q Q
  have h := ((Algebra.isUnramifiedAt_iff_map_eq R q Q).mp inferInstance).2
  change (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map
    (algebraMap (Localization.AtPrime q) (Localization.AtPrime Q)) = _
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact h

/-- Order preservation holds for every ideal of the source local ring,
including residual ideals obtained by local boundary factor extraction.
Neither ideal descent to the affine source nor closedness of the points is required. -/
theorem pointed_etale_local_ideal_order_iff (f : R →+* S) (hf : f.Etale)
    (q : Ideal R) (Q : Ideal S) [q.IsPrime] [Q.IsPrime] (hQ : q = Q.comap f)
    (J : Ideal (Localization.AtPrime q)) (b : ℕ) :
    J.map (Localization.localRingHom q Q f hQ) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ b ↔
      J ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b := by
  have hflat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1
  have hfaithful := Boundary.FactorNaturality.Construction.pointed_flat_localRingHom_faithfullyFlat f hflat q Q hQ
  rw [← pointed_etale_local_maximalIdeal_map f hf q Q hQ, ← Ideal.map_pow]
  exact Boundary.FactorNaturality.Construction.faithfullyFlat_map_ideal_le_iff _ hfaithful _ _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.EtaleLocalOrder.Construction
