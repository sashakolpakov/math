import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime
import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic

/-! # Finite Padic Commutation -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation.Realization

noncomputable section

/-! Commutation with a one-prime factor is determined by its local projection. -/

open scoped Classical
open IsDedekindDomain

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem finiteSymplectic_padic_ext {g h : Theta.PoissonAutomorphyNormalizationData.Sp I Theta.PoissonAutomorphyNormalizationData.AQf}
    (he : ∀ (q : ℕ) [Fact q.Prime],
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g = Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom h) : g = h := by
  apply FiniteMaskCoordinates.Realization.finiteSymplectic_ext
  intro v
  let q := (Rat.HeightOneSpectrum.primesEquiv v).val
  let : Fact q.Prime := ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩
  have hv : FiniteSchur.Realization.rationalPrime q = v := FinitePrimePadic.Realization.rationalPrime_of_place v
  have hp := congrArg (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom) (he q)
  rw [SymplecticMapComp.Realization.mapSp_comp, SymplecticMapComp.Realization.mapSp_comp, FinitePrimePadic.Realization.finitePadicCoordinate_projection, hv] at hp
  exact hp

theorem finitePadicSymplecticInclusion_commute (q : ℕ) [Fact q.Prime]
    (A : Theta.PoissonAutomorphyNormalizationData.Sp I ℚ_[q]) (g : Theta.PoissonAutomorphyNormalizationData.Sp I Theta.PoissonAutomorphyNormalizationData.AQf)
    (hA : Commute A (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g)) :
    Commute (FiniteConjugation.Realization.finitePadicSymplecticInclusion q A) g := by
  apply finiteSymplectic_padic_ext
  intro p hp
  rw [map_mul, map_mul]
  by_cases hpq : p = q
  · subst p
    rw [FiniteConjugation.Realization.finitePadicSymplecticInclusion_projection]
    exact hA
  · rw [FinitePadicOtherPrime.Realization.finitePadicSymplecticInclusion_other_prime q p hpq, one_mul, mul_one]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicCommutation.Realization
