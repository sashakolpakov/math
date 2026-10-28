import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime

/-! # Prime Determination -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PrimeDetermination.CM

noncomputable section

/-! All rational-prime projections determine a finite symplectic
matrix. A matrix supported at one prime is its literal local inclusion. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem map_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) : Function.Injective (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (ι := I) f) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  exact hf (congrFun (congrFun (congrArg Subtype.val h) i) j)

theorem to_prime (p : ℕ) [Fact p.Prime] (A B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (h : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom A = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom B) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p)) A = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePrimeEval (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p)) B := by
  apply map_injective (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm.toRingHom (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm.injective
  rw [RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp.Realization.mapSp_comp, RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp.Realization.mapSp_comp]
  exact h

theorem ext (A B : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (h : ∀ (p : ℕ) [Fact p.Prime],
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom A = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom B) : A = B := by
  apply RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro v
  obtain ⟨⟨p, hp⟩, rfl⟩ := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.surjective v
  let : Fact p.Prime := ⟨hp⟩
  exact to_prime p A B (h p)

theorem supported (q : ℕ) [Fact q.Prime] (A : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (S : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q])
    (hq : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q).toRingHom A = S)
    (hother : ∀ (p : ℕ) [Fact p.Prime], p ≠ q → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.mapSp (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p).toRingHom A = 1) :
    A = RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion q S := by
  apply CM.ext
  intro p hp
  by_cases hpq : p = q
  · subst p
    exact hq.trans (RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection q S).symm
  · exact (hother p hpq).trans (RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq S).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.PrimeDetermination.CM
