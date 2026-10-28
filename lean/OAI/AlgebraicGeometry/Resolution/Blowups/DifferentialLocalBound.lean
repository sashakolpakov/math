import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Derivation
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Differential Local Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound.Construction

/-! A global differential unit ideal bounds order at every prime, without closed-point restrictions. -/

variable {R : Type*} [CommRing R]

/-- If the differential ideal becomes the unit ideal after `n` steps,
the local order is at most `n` at every prime. -/
theorem local_order_lt_of_differential_top (J : Ideal R) (n : ℕ)
    (hn : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J n = ⊤) (q : Ideal R) [q.IsPrime] :
    ¬ J.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (n + 1) := by
  intro h
  let T := Localization.AtPrime q
  let : Algebra.FormallyEtale R T := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  have htop := Etale.Derivation.Construction.iteratedDifferentialIdeal_map_le_of_etale (S := T) J n
  rw [hn, Ideal.map_top] at htop
  have hpow := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow (IsLocalRing.maximalIdeal T)
    (J.map (algebraMap R T)) 1 n (by simpa only [Nat.add_comm 1 n] using h)
  rw [pow_one] at hpow
  exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp (htop.trans hpow))

end OAI.AlgebraicGeometry.Resolution.Blowups.DifferentialLocalBound.Construction
