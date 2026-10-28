import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Norm
import Mathlib.RingTheory.LocalRing.Length

/-! # Semilocal Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNorm

noncomputable section

/-!
# ProjectionFormula: norm multiplicities with several primes above a local point

Unlike the local extension calculation, this module permits a finite
Dedekind algebra with several maximal ideals above the base DVR. Its norm
exponent is the sum of their residue degrees, counted with the multiplicities
in the actual prime-ideal factorization.
-/

open IsLocalRing UniqueFactorizationMonoid
open scoped Classical

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain R]
  [IsDiscreteValuationRing R] [IsDedekindDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
  [PerfectField (FractionRing R)]

/-- Every nonzero prime above a DVR contributes its own residue degree. -/
theorem relNorm_prime (P : Ideal S) (hP : Prime P) :
    Ideal.relNorm R P = maximalIdeal R ^ P.inertiaDeg R := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hunder : P.under R = maximalIdeal R := eq_maximalIdeal inferInstance
  let : P.LiesOver (maximalIdeal R) :=
    hunder ▸ inferInstanceAs (P.LiesOver (P.under R))
  exact Ideal.relNorm_eq_pow_of_isMaximal P (maximalIdeal R)

/-- The sum uses the multiset of prime factors, so repeated factors retain
their divisor multiplicities. -/
def normMultiplicity (R : Type*) [CommRing R] [Algebra R S] (I : Ideal S) : ℕ :=
  ((normalizedFactors I).map (fun P => P.inertiaDeg R)).sum

theorem relNorm_eq_maximal_pow (I : Ideal S) (hI : I ≠ ⊥) :
    Ideal.relNorm R I = maximalIdeal R ^ normMultiplicity R I := by
  have hprod : ∀ l : Multiset (Ideal S), (∀ P ∈ l, Prime P) →
      Ideal.relNorm R l.prod = maximalIdeal R ^ (l.map (fun P => P.inertiaDeg R)).sum := by
    intro l
    induction l using Multiset.induction_on with
    | empty => simp
    | @cons P l ih =>
      intro h
      rw [Multiset.prod_cons, map_mul, relNorm_prime P (h P (Multiset.mem_cons_self P l)),
        ih (fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)),
        Multiset.map_cons, Multiset.sum_cons, pow_add]
  have hfactor : (normalizedFactors I).prod = I := by
    simpa only [normalize_eq] using prod_normalizedFactors_eq hI
  change Ideal.relNorm R I =
    maximalIdeal R ^ ((normalizedFactors I).map (fun P => P.inertiaDeg R)).sum
  simpa only [hfactor] using hprod (normalizedFactors I) (prime_of_normalized_factor)

/-- Norm of a nonzero element: sum all source-prime multiplicities weighted
by their native residue-field degrees. -/
theorem ord_intNorm_eq_normMultiplicity (a : S) (ha : a ≠ 0) :
    Ring.ord R (Algebra.intNorm R S a) =
      (normMultiplicity R (Ideal.span {a}) : ℕ∞) := by
  have hspan : Ideal.span ({a} : Set S) ≠ ⊥ := by
    exact fun h => ha (Ideal.span_singleton_eq_bot.mp h)
  have h := relNorm_eq_maximal_pow (R := R) (Ideal.span {a}) hspan
  rw [Ideal.relNorm_singleton] at h
  change Module.length R (R ⧸ Ideal.span {Algebra.intNorm R S a}) = _
  rw [h, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

attribute [local instance] FractionRing.liftAlgebra

/-- The integer order of the field norm of a rational function is the
residue-weighted source multiplicity, including both zeros and poles and
all branches above the base point. -/
theorem log_ordFrac_norm_div (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm (FractionRing R)
      (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b))) =
        (normMultiplicity R (Ideal.span {a}) : ℤ) -
          (normMultiplicity R (Ideal.span {b}) : ℤ) := by
  rw [div_eq_mul_inv, map_mul, Algebra.norm_inv, ← div_eq_mul_inv,
    ← Algebra.algebraMap_intNorm_fractionRing,
    ← Algebra.algebraMap_intNorm_fractionRing, map_div₀,
    Ring.ordFrac_eq_ord R (Algebra.intNorm_ne_zero.mpr ha),
    Ring.ordFrac_eq_ord R (Algebra.intNorm_ne_zero.mpr hb),
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_of_ne_zero (Algebra.intNorm_ne_zero.mpr ha))
      (ord_intNorm_eq_normMultiplicity a ha),
    Ring.ordMonoidWithZeroHom_eq_coe R
      (mem_nonZeroDivisors_of_ne_zero (Algebra.intNorm_ne_zero.mpr hb))
      (ord_intNorm_eq_normMultiplicity b hb)]
  exact WithZero.log_div (by simp) (by simp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNorm
