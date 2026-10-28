import OAI.AlgebraicGeometry.CycleClass.Thom.BranchOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Local

/-! # Semilocal Divisor Norm -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.SemilocalDivisorNorm.Constructions

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
      (BranchOrder.Constructions.ord_eq_count P.asIdeal P.ne_bot a ha),
    Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hb')
      (BranchOrder.Constructions.ord_eq_count P.asIdeal P.ne_bot b hb)]
  exact WithZero.log_div (by simp) (by simp)

theorem normMultiplicity_eq_sum_counts
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    [Fintype (HeightOneSpectrum S)] (a : S) (ha : a ≠ 0) :
    ((normalizedFactors (Ideal.span ({a} : Set S))).map (fun P => P.inertiaDeg R)).sum =
      ∑ P : HeightOneSpectrum S, P.asIdeal.inertiaDeg R *
        (normalizedFactors (Ideal.span ({a} : Set S))).count P.asIdeal := by
  have h := BranchOrder.Constructions.length_eq_sum_local_orders R a ha
  rw [SemilocalLength.Constructions.length_quotient_eq_sum _
    (fun h => ha (Ideal.span_singleton_eq_bot.mp h))] at h
  simp_rw [BranchOrder.Constructions.ord_eq_count _ (HeightOneSpectrum.ne_bot _) a ha] at h
  exact_mod_cast h

end AlgebraicGeometry.CycleClass.Thom.SemilocalDivisorNorm.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.SemilocalDivisorNorm.Constructions.Normalization

/-! The divisor of a rational function on a possibly singular local curve
is the sum of its orders on the finite normal branches, weighted by the
actual residue-field degrees. The fraction field is shared by construction. -/

open IsDedekindDomain
open scoped Classical BigOperators

variable (R S K : Type*) [CommRing R] [CommRing S] [IsDomain R]
  [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDedekindDomain S] [Field K] [Algebra R S] [Module.Finite R S]
  [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  [IsFractionRing R K] [IsFractionRing S K]

include K in
omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [IsDedekindDomain S] [Module.Finite R S] [IsFractionRing S K] in
theorem algebraMap_injective : Function.Injective (algebraMap R S) := by
  apply Function.Injective.of_comp (f := algebraMap S K)
  simpa only [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq] using
    IsFractionRing.injective R K

omit [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
  [Module.Finite R S] in
theorem localOrder_div (P : HeightOneSpectrum S) (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    localOrder P ((FractionRing.algEquiv S K).symm
      (algebraMap R K a / algebraMap R K b)) =
      ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({algebraMap R S a} : Set S))).count P.asIdeal : ℤ) -
        ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({algebraMap R S b} : Set S))).count P.asIdeal : ℤ) := by
  rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K,
    map_div₀, AlgEquiv.commutes, AlgEquiv.commutes]
  exact Constructions.localOrder_div P (algebraMap R S a) (algebraMap R S b)
    ((map_ne_zero_iff _ (algebraMap_injective R S K)).mpr ha)
    ((map_ne_zero_iff _ (algebraMap_injective R S K)).mpr hb)

theorem log_ordFrac_eq_sum [Fintype (HeightOneSpectrum S)] (f : K) (hf : f ≠ 0) :
    WithZero.log (Ring.ordFrac R f) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
        localOrder P ((FractionRing.algEquiv S K).symm f) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have haS : algebraMap R S a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective R S K)).mpr ha
  have hbS : algebraMap R S b ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective R S K)).mpr hb'
  rw [Normalization.Local.Constructions.Divisor.log_ordFrac_div (S := S) a b ha hb']
  change (Normalization.Local.Constructions.Divisor.branchMultiplicity R S a : ℤ) -
    (Normalization.Local.Constructions.Divisor.branchMultiplicity R S b : ℤ) = _
  unfold Normalization.Local.Constructions.Divisor.branchMultiplicity
  rw [normMultiplicity_eq_sum_counts R _ haS,
    normMultiplicity_eq_sum_counts R _ hbS]
  simp_rw [localOrder_div R S K _ a b ha hb']
  simp only [Nat.cast_sum, Nat.cast_mul, mul_sub, Finset.sum_sub_distrib]

/-- The finite branch set is obtained from the finite birational extension. -/
theorem log_ordFrac_normalization (f : K) (hf : f ≠ 0) :
    letI : Finite (HeightOneSpectrum S) := BranchOrder.Constructions.finite_heightOneSpectrum R S
    letI := Fintype.ofFinite (HeightOneSpectrum S)
    WithZero.log (Ring.ordFrac R f) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
        localOrder P ((FractionRing.algEquiv S K).symm f) := by
  let : Finite (HeightOneSpectrum S) := BranchOrder.Constructions.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  exact log_ordFrac_eq_sum R S K f hf

end AlgebraicGeometry.CycleClass.Thom.SemilocalDivisorNorm.Constructions.Normalization

end

end OAI
