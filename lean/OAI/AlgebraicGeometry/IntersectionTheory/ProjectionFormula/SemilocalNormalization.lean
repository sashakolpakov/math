import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalDivisorNorm
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Divisor

/-! # Semilocal Normalization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNormalization

noncomputable section

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
    SemilocalDivisorNorm.localOrder P ((FractionRing.algEquiv S K).symm
      (algebraMap R K a / algebraMap R K b)) =
      ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({algebraMap R S a} : Set S))).count P.asIdeal : ℤ) -
        ((UniqueFactorizationMonoid.normalizedFactors
          (Ideal.span ({algebraMap R S b} : Set S))).count P.asIdeal : ℤ) := by
  rw [IsScalarTower.algebraMap_apply R S K, IsScalarTower.algebraMap_apply R S K,
    map_div₀, AlgEquiv.commutes, AlgEquiv.commutes]
  exact SemilocalDivisorNorm.localOrder_div P (algebraMap R S a) (algebraMap R S b)
    ((map_ne_zero_iff _ (algebraMap_injective R S K)).mpr ha)
    ((map_ne_zero_iff _ (algebraMap_injective R S K)).mpr hb)

theorem log_ordFrac_eq_sum [Fintype (HeightOneSpectrum S)] (f : K) (hf : f ≠ 0) :
    WithZero.log (Ring.ordFrac R f) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
        SemilocalDivisorNorm.localOrder P ((FractionRing.algEquiv S K).symm f) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have haS : algebraMap R S a ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective R S K)).mpr ha
  have hbS : algebraMap R S b ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective R S K)).mpr hb'
  rw [Normalization.Divisor.log_ordFrac_div (S := S) a b ha hb']
  change (SemilocalNorm.normMultiplicity R (Ideal.span {algebraMap R S a}) : ℤ) -
    (SemilocalNorm.normMultiplicity R (Ideal.span {algebraMap R S b}) : ℤ) = _
  rw [SemilocalDivisorNorm.normMultiplicity_eq_sum_counts R _ haS,
    SemilocalDivisorNorm.normMultiplicity_eq_sum_counts R _ hbS]
  simp_rw [localOrder_div R S K _ a b ha hb']
  simp only [Nat.cast_sum, Nat.cast_mul, mul_sub, Finset.sum_sub_distrib]

/-- The finite branch set is obtained from the finite birational extension. -/
theorem log_ordFrac_normalization (f : K) (hf : f ≠ 0) :
    letI : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
    letI := Fintype.ofFinite (HeightOneSpectrum S)
    WithZero.log (Ring.ordFrac R f) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℤ) *
        SemilocalDivisorNorm.localOrder P ((FractionRing.algEquiv S K).symm f) := by
  let : Finite (HeightOneSpectrum S) := BranchOrder.finite_heightOneSpectrum R S
  let := Fintype.ofFinite (HeightOneSpectrum S)
  exact log_ordFrac_eq_sum R S K f hf

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalNormalization
