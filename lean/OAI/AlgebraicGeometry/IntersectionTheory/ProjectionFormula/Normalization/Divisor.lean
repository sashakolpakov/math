import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Colength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Normalization

/-! # Divisor -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Divisor

noncomputable section

/-!
# ProjectionFormula: local divisor multiplicities under finite normalization

The original local domain may be singular and its normalization may have
several branches. Quotient lengths express the original order as the sum
of the residue degrees of the prime factors in the normalization.
-/

open UniqueFactorizationMonoid

variable {R S K : Type*} [CommRing R] [CommRing S] [IsDomain R]
  [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDedekindDomain S] [Field K] [Algebra R S] [Module.Finite R S]
  [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [IsFractionRing R K] [IsFractionRing S K]

/-- The prime factors are taken in the normalization, with multiplicity. -/
def branchMultiplicity (R S : Type*) [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (a : R) : ℕ :=
  ((normalizedFactors (Ideal.span ({algebraMap R S a} : Set S))).map
    (fun P => P.inertiaDeg R)).sum

include K in
theorem ord_eq_branchMultiplicity (a : R) (ha : a ≠ 0) :
    Ring.ord R a = (branchMultiplicity R S a : ℕ∞) := by
  have hi : Function.Injective (algebraMap R S) := by
    apply Function.Injective.of_comp (f := algebraMap S K)
    simpa only [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq] using
      IsFractionRing.injective R K
  rw [ProjectionFormula.Finite.Colength.ord_eq_length_birational_extension R S K a ha]
  exact SemilocalLength.length_quotient_eq_sum _
    (fun h => ha (hi (by simpa using Ideal.span_singleton_eq_bot.mp h)))

/-- The corresponding equality for a rational function includes both zeros
and poles, using the same integer-valued order as the geometric divisor. -/
theorem log_ordFrac_div (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R K a / algebraMap R K b)) =
      (branchMultiplicity R S a : ℤ) - (branchMultiplicity R S b : ℤ) := by
  rw [map_div₀, Ring.ordFrac_eq_ord R ha, Ring.ordFrac_eq_ord R hb,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero ha)
      (ord_eq_branchMultiplicity (S := S) (K := K) a ha),
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hb)
      (ord_eq_branchMultiplicity (S := S) (K := K) b hb)]
  exact WithZero.log_div (by simp) (by simp)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Divisor
