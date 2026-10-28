import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimeProduct
import OAI.RepresentationTheory.Hecke.RadialDilation.SymplecticMapComp

/-! # Finite Prime Padic -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic.Realization

noncomputable section

/-! Identify a one-prime matrix factor with its p-adic coordinate realization. -/

open scoped Classical _root_.Matrix
open _root_.Matrix IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finitePadicCoordinate_projection (q : ℕ) [Fact q.Prime] :
    (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom.comp (FiniteSchur.Realization.finitePadicProjection q).toRingHom =
      FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) := by
  apply RingHom.ext
  intro a
  change (FiniteSchur.Realization.padicCoordinateEquiv q)
    ((FiniteSchur.Realization.padicCoordinateEquiv q).symm (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q) a)) = _
  exact (FiniteSchur.Realization.padicCoordinateEquiv q).apply_symm_apply _

theorem finitePrimePart_padic (q : ℕ) [Fact q.Prime] (g : Theta.PoissonAutomorphyNormalizationData.Sp ι Theta.PoissonAutomorphyNormalizationData.AQf) :
    FinitePrimeProduct.Realization.finitePrimePart g (FiniteSchur.Realization.rationalPrime q) =
      FiniteConjugation.Realization.finitePadicSymplecticInclusion q (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g) := by
  have h : Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g) =
      Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q)) g := by
    rw [SymplecticMapComp.Realization.mapSp_comp, finitePadicCoordinate_projection]
  change FiniteConjugation.Realization.finitePrimeSymplecticInclusion (FiniteSchur.Realization.rationalPrime q) (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePrimeEval (FiniteSchur.Realization.rationalPrime q)) g) =
    FiniteConjugation.Realization.finitePrimeSymplecticInclusion (FiniteSchur.Realization.rationalPrime q)
      (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.padicCoordinateEquiv q).toRingHom (Theta.PoissonAutomorphyNormalizationData.mapSp (FiniteSchur.Realization.finitePadicProjection q).toRingHom g))
  rw [h]

local instance c410FinitePrimePadicPart_prime (v : HeightOneSpectrum ℤ) :
    Fact (Rat.HeightOneSpectrum.primesEquiv v).val.Prime :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv v).property⟩

theorem rationalPrime_of_place (v : HeightOneSpectrum ℤ) :
    FiniteSchur.Realization.rationalPrime (Rat.HeightOneSpectrum.primesEquiv v).val = v := by
  change (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm
    (Rat.HeightOneSpectrum.primesEquiv v) = v
  exact (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm_apply_apply v

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FinitePrimePadic.Realization
