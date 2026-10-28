import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PrimeOrderNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfacePointLift
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Persistent Locus Descent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PersistentLocusDescent.Construction

noncomputable section

/-! A resolved order locus descends from an étale refinement covering its persistent hypersurface. -/

variable (k : Type*) {R V : Type*} [CommRing k] [CommRing R] [CommRing V] [Algebra k R]

/-- The maximal-contact equation contains every prime of high local order,
without assuming that the prime is closed or replacing local order by an ordinary ideal power. -/
theorem relative_hypersurface_contains_local_order_locus (J : Ideal R) (z : R) (n : ℕ)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) (q : Ideal R) [q.IsPrime]
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1)) : z ∈ q := by
  let T := Localization.AtPrime q
  let : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have hzordinary : z ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n :=
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J n hz
  have hzT : algebraMap R T z ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (J.map (algebraMap R T)) n :=
    Blowups.Etale.Derivation.Construction.iteratedDifferentialIdeal_map_le_of_etale (S := T) J n
      (Ideal.mem_map_of_mem (algebraMap R T) hzordinary)
  have hpow := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (IsLocalRing.maximalIdeal T)
    (J.map (algebraMap R T)) 1 n (by simpa only [Nat.add_comm 1 n] using hJ)
  rw [pow_one] at hpow
  have hmem : z ∈ (IsLocalRing.maximalIdeal T).comap (algebraMap R T) := hpow hzT
  have hcomap : (IsLocalRing.maximalIdeal T).comap (algebraMap R T) = q :=
    Localization.AtPrime.under_maximalIdeal (I := q)
  exact hcomap ▸ hmem

/-- No high-order primes can remain downstairs when the actual étale
refinement covers its persistent hypersurface and has no high-order primes. -/
theorem persistent_order_bound_descends_from_hypersurface_refinement
    (J : Ideal R) (z : R) (n : ℕ) (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (w : V) (g : R →+* V) (hg : g.Etale)
    (e : (V ⧸ Ideal.span {w}) ≃+* (R ⧸ Ideal.span {z}))
    (he : e.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {w})).comp g) =
      Ideal.Quotient.mk (Ideal.span {z}))
    (hclear : ∀ (Q : Ideal V) [Q.IsPrime], ¬ (J.map g).map (algebraMap V (Localization.AtPrime Q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) ^ (n + 1))
    (q : Ideal R) [q.IsPrime] : ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
  intro hq
  have hzq := relative_hypersurface_contains_local_order_locus k J z n hz q hq
  obtain ⟨Q, hQ, hQg⟩ := HypersurfacePointLift.Construction.hypersurface_isomorphism_covers_primes z w g e he q hzq
  let : Q.IsPrime := hQ
  exact hclear Q ((Blowups.Etale.PrimeOrderNaturality.Construction.etale_map_prime_order_iff g hg J q Q hQg.symm (n + 1)).mpr hq)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PersistentLocusDescent.Construction
