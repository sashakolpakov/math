import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralInclusion

/-! # Adelic Coordinate Split -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicCoordinateSplit.TestTransport

noncomputable section

section

/-! Integrality in the actual rational finite adeles is equivalent to
integrality under every prescribed p-adic projection. -/

open scoped Classical
open IsDedekindDomain

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

theorem integralFiniteAdeles_padic_iff (a : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) :
    a ∈ AbelianModuli.ReferenceFamily.AdelicData.integralFiniteAdeles ↔ ∀ (p : ℕ) [Fact p.Prime], ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p a‖ ≤ 1 := by
  constructor
  · intro ha p hp
    exact RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_integral_norm p a ha
  · intro ha v
    obtain ⟨⟨p, hp⟩, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.surjective v
    let : Fact p.Prime := ⟨hp⟩
    let z : PadicInt p := ⟨RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p a, ha p⟩
    have hz := PadicIntegralInclusion.TestTransport.padicCoordinate_integer_mem p z
    have he : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p (z : Padic p) = a (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p) :=
      (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).apply_symm_apply _
    exact he ▸ hz

end

/-! Separate integrality at the selected prime from all remaining
primes, retaining the given rational coordinates. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicData OAI.RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization

theorem indexed_prime_predicate_split {J : Type*} (q : ℕ) [Fact q.Prime]
    (P Q : J → (p : ℕ) → [Fact p.Prime] → Prop)
    (h : ∀ j (p : ℕ) [Fact p.Prime], p ≠ q → (P j p ↔ Q j p)) :
    (∀ j (p : ℕ) [Fact p.Prime], P j p) ↔
      (∀ j (p : ℕ) [Fact p.Prime], p ≠ q → Q j p) ∧ ∀ j, P j q := by
  constructor
  · intro hP
    exact ⟨fun j p hp hpq => (h j p hpq).mp (hP j p), fun j => hP j q⟩
  · rintro ⟨hQ, hq⟩ j p hp
    by_cases hpq : p = q
    · subst p
      exact hq j
    · exact (h j p hpq).mpr (hQ j p hpq)

theorem adelic_coordinate_norm_split {J : Type*} (q : ℕ) [Fact q.Prime]
    (z : J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) (y : J → ℚ)
    (h : ∀ j (p : ℕ) [Fact p.Prime], p ≠ q →
      RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (z j) = algebraMap ℚ (Padic p) (y j)) :
    (∀ j (p : ℕ) [Fact p.Prime], ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (z j)‖ ≤ 1) ↔
      (∀ j (p : ℕ) [Fact p.Prime], p ≠ q → ‖(y j : Padic p)‖ ≤ 1) ∧
        ∀ j, ‖RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (z j)‖ ≤ 1 :=
  indexed_prime_predicate_split q _ _ (fun j p _hp hpq =>
    Iff.of_eq (congrArg (fun a : Padic p => ‖a‖ ≤ 1) (h j p hpq)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.AdelicCoordinateSplit.TestTransport
