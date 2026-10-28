import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BranchOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNorm

/-! # Semilocal Divisor Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm

noncomputable section

/-! The norm formula written in the actual integer orders at every source
prime. Several branches and negative orders are included. -/

open IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

def localOrder (P : HeightOneSpectrum S) (f : FractionRing S) : ℤ :=
  letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    S P.ne_bot (Localization.AtPrime P.asIdeal)
  WithZero.log (Ring.ordFrac (Localization.AtPrime P.asIdeal) f)

theorem localOrder_div (P : HeightOneSpectrum S) (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) :
    localOrder P (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b) =
      ((normalizedFactors (Ideal.span ({a} : Set S))).count P.asIdeal : ℤ) -
        ((normalizedFactors (Ideal.span ({b} : Set S))).count P.asIdeal : ℤ) := by
  let A := Localization.AtPrime P.asIdeal
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S P.ne_bot A
  have hi : Function.Injective (algebraMap S A) :=
    IsLocalization.injective A P.asIdeal.primeCompl_le_nonZeroDivisors
  have ha' : algebraMap S A a ≠ 0 := (map_ne_zero_iff _ hi).mpr ha
  have hb' : algebraMap S A b ≠ 0 := (map_ne_zero_iff _ hi).mpr hb
  change WithZero.log (Ring.ordFrac A _) = _
  rw [IsScalarTower.algebraMap_apply S A (FractionRing S),
    IsScalarTower.algebraMap_apply S A (FractionRing S), map_div₀,
    Ring.ordFrac_eq_ord A ha', Ring.ordFrac_eq_ord A hb',
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero ha')
      (BranchOrder.ord_eq_count P.asIdeal P.ne_bot a ha),
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hb')
      (BranchOrder.ord_eq_count P.asIdeal P.ne_bot b hb)]
  exact WithZero.log_div (by simp) (by simp)

theorem normMultiplicity_eq_sum_counts
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    [Fintype (HeightOneSpectrum S)] (a : S) (ha : a ≠ 0) :
    SemilocalNorm.normMultiplicity R (Ideal.span {a}) =
      ∑ P : HeightOneSpectrum S, P.asIdeal.inertiaDeg R *
        (normalizedFactors (Ideal.span ({a} : Set S))).count P.asIdeal := by
  have h := BranchOrder.length_eq_sum_local_orders R a ha
  rw [SemilocalLength.length_quotient_eq_sum _
    (fun h => ha (Ideal.span_singleton_eq_bot.mp h))] at h
  simp_rw [BranchOrder.ord_eq_count _ (HeightOneSpectrum.ne_bot _) a ha] at h
  exact_mod_cast h

attribute [local instance] FractionRing.liftAlgebra

/-- The full local norm-divisor formula for a finite normal algebra over a
DVR: sum all branch orders with their residue-field degrees. -/
theorem log_ordFrac_norm_eq_sum
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [PerfectField (FractionRing R)] [Fintype (HeightOneSpectrum S)]
    (a b : S) (ha : a ≠ 0) (hb : b ≠ 0) :
    WithZero.log (Ring.ordFrac R (Algebra.norm (FractionRing R)
      (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b))) =
        ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
          localOrder P (algebraMap S (FractionRing S) a / algebraMap S (FractionRing S) b) := by
  rw [SemilocalNorm.log_ordFrac_norm_div a b ha hb,
    normMultiplicity_eq_sum_counts R a ha, normMultiplicity_eq_sum_counts R b hb]
  simp_rw [localOrder_div _ a b ha hb]
  simp only [Nat.cast_sum, Nat.cast_mul, mul_sub, Finset.sum_sub_distrib]

/-- The local norm formula for every nonzero rational function. The finite
set of source branches is supplied by module finiteness over the local base. -/
theorem log_ordFrac_norm
    (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [PerfectField (FractionRing R)] (f : FractionRing S) (hf : f ≠ 0) :
    letI : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
    letI := Fintype.ofFinite (HeightOneSpectrum S)
    WithZero.log (Ring.ordFrac R (Algebra.norm (FractionRing R) f)) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) * localOrder P f := by
  let : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective S f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  exact log_ordFrac_norm_eq_sum R a b ha (mem_nonZeroDivisors_iff_ne_zero.mp hb)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm
