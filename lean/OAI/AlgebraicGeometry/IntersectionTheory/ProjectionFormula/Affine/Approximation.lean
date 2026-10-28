import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DedekindApproximation
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Order

/-! # Approximation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Approximation

noncomputable section

/-! Finite approximation for the native scheme orders on the spectrum of a
Dedekind domain. The prescribed integers are orders in the actual principal
divisor, through the canonical function-field identification. -/

open _root_.AlgebraicGeometry IsDedekindDomain UniqueFactorizationMonoid WithZero

universe u v

variable (R : Type u) [CommRing R] [IsDedekindDomain R]

theorem intValuation_eq_count (P : HeightOneSpectrum R) (a : R) (ha : a ≠ 0) :
    P.intValuation a = exp (-((normalizedFactors (Ideal.span ({a} : Set R))).count
      P.asIdeal : ℤ)) := by
  rw [P.intValuation_eq_exp_neg_multiplicity ha,
    multiplicity_eq_count_normalizedFactors P.irreducible
      (fun h => ha (Ideal.span_singleton_eq_bot.mp h)),
    normalize_eq]

theorem valuation_eq_localOrder (P : HeightOneSpectrum R) (f : FractionRing R)
    (hf : f ≠ 0) :
    P.valuation (FractionRing R) f = exp (-SemilocalDivisorNorm.localOrder P f) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R f
  have ha : a ≠ 0 := fun ha => hf (by simp [ha])
  have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  rw [SemilocalDivisorNorm.localOrder_div P a b ha hb', map_div₀,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_eq_count R P a ha, intValuation_eq_count R P b hb', ← exp_sub]
  congr 1
  ring

theorem exists_local_orders {ι : Type v} [Fintype ι]
    (P : ι → HeightOneSpectrum R) (hP : Function.Injective P) (e : ι → ℤ) :
    ∃ f : FractionRing R, f ≠ 0 ∧ ∀ i, SemilocalDivisorNorm.localOrder (P i) f = e i := by
  obtain ⟨f, hf, he⟩ :=
    DedekindApproximation.exists_fractional_orders R (FractionRing R) P hP e
  refine ⟨f, hf, fun i => ?_⟩
  have h := he i
  rw [valuation_eq_localOrder R (P i) f hf, exp_inj, neg_inj] at h
  exact h

theorem exists_scheme_orders {ι : Type v} [Fintype ι]
    (P : ι → HeightOneSpectrum R) (hP : Function.Injective P) (e : ι → ℤ) :
    ∃ f : (Spec (.of R)).functionField, f ≠ 0 ∧
      ∀ i, (Spec (.of R)).ord f (Order.branchPoint R (P i)) = e i := by
  obtain ⟨f, hf, he⟩ := exists_local_orders R P hP e
  refine ⟨Order.affineFunctionFieldIso R f, ?_, ?_⟩
  · exact (map_ne_zero (Order.affineFunctionFieldIso R)).mpr hf
  · intro i
    rw [Order.schemeOrder_eq_localOrder, he]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.Approximation
