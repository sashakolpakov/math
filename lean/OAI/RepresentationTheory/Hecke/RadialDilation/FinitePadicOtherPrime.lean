import OAI.RepresentationTheory.Hecke.RadialDilation.FiniteMaskCoordinates
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp

/-! # Finite Padic Other Prime -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization

noncomputable section

/-! Projection of a one-prime symplectic factor at another rational prime. -/

open scoped Classical
open IsDedekindDomain

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem finitePadicSymplecticInclusion_other_place (q : ℕ) [Fact q.Prime]
    (v : HeightOneSpectrum ℤ) (hv : v ≠ FiniteSchur.Realization.rationalPrime q) (g : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval v) (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g) = 1 :=
  FiniteMaskCoordinates.Realization.finitePrimeSymplecticInclusion_other (FiniteSchur.Realization.rationalPrime q) v hv _

theorem rationalPrime_ne (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q) :
    FiniteSchur.Realization.rationalPrime p ≠ FiniteSchur.Realization.rationalPrime q := by
  intro h
  have he := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm.injective h
  exact hpq (congrArg Subtype.val he)

theorem finitePadicSymplecticInclusion_other_prime (q p : ℕ) [Fact q.Prime] [Fact p.Prime]
    (hpq : p ≠ q) (g : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) :
    Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection p).toRingHom (FiniteConjugation.Realization.finitePadicSymplecticInclusion q g) = 1 := by
  have h := finitePadicSymplecticInclusion_other_place q (FiniteSchur.Realization.rationalPrime p) (rationalPrime_ne p q hpq) g
  have hm := congrArg (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv p).symm.toRingHom) h
  rw [SymplecticMapComp.Realization.mapSp_comp, map_one] at hm
  exact hm

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization
