import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualControl
import OAI.AlgebraicGeometry.Resolution.Blowups.PersistentLocusDescent

/-! # Residual Drop All Primes -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ResidualDropAllPrimes.Construction

noncomputable section

/-! The residual phase terminal identity lowers local order at every prime. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- High local order forces the entire relative differential ideal into
the prime, including when the prime is not a closed point. -/
theorem relative_differential_control_le_prime_of_local_order
    (J q : Ideal R) [q.IsPrime] (b : ℕ) (hb : 0 < b)
    (hJ : J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (b - 1) ≤ q := by
  intro z hz
  exact PersistentLocusDescent.Construction.relative_hypersurface_contains_local_order_locus k J z (b - 1) hz q
    (by simpa only [Nat.sub_add_cancel hb] using hJ)

/-- The native terminal sum identity excludes residual order `m` at every
prime where the product still has order at least its fixed control `b`. -/
theorem residual_terminal_drop_at_every_prime (M J : Ideal R) (m b : ℕ)
    (hm : 0 < m) (hb : 0 < b)
    (hdrop : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (M * J) (b - 1) ⊔
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m - 1) = ⊤)
    (q : Ideal R) [q.IsPrime]
    (hprod : (M * J).map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b) :
    ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ m := by
  intro hJ
  have hle := sup_le
    (relative_differential_control_le_prime_of_local_order k (M * J) q b hb hprod)
    (relative_differential_control_le_prime_of_local_order k J q m hm hJ)
  rw [hdrop] at hle
  exact (inferInstance : q.IsPrime).ne_top (top_le_iff.mp hle)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ResidualDropAllPrimes.Construction
