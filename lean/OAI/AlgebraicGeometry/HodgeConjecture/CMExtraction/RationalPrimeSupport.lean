import OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime

/-! # Rational Prime Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPrimeSupport.TestTransport

noncomputable section

/-! An adele supported at one rational prime has zero projection at
every other prime, also after any finite-adele linear map. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization

variable (q : ℕ) [Fact q.Prime]

def rationalPrimeIdempotent : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf := RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicInclusion q 1

theorem rationalPrimeIdempotent_same :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection q (rationalPrimeIdempotent q) = 1 :=
  RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection_inclusion q 1

theorem rationalPrimeIdempotent_other (p : ℕ) [Fact p.Prime] (hpq : p ≠ q) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (rationalPrimeIdempotent q) = 0 := by
  have h := RepresentationTheory.Hecke.RadialDilation.FiniteConjugation.Realization.finitePrimeEval_include_other (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime q) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.rationalPrime p)
    (RepresentationTheory.Hecke.RadialDilation.FinitePadicOtherPrime.Realization.rationalPrime_ne p q hpq) (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv q 1)
  exact (congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.padicCoordinateEquiv p).symm h).trans (map_zero _)

theorem supported_adele_projection_zero (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    (x : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (hx : rationalPrimeIdempotent q * x = x) : RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p x = 0 := by
  have h := congrArg (RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p) hx
  rw [map_mul, rationalPrimeIdempotent_other q p hpq, zero_mul] at h
  exact h.symm

theorem supported_linear_difference (p : ℕ) [Fact p.Prime] (hpq : p ≠ q)
    {V : Type*} [AddCommGroup V] [Module RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf V] (f : V →ₗ[RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)
    (x y : V) (h : rationalPrimeIdempotent q • (x - y) = x - y) :
    RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (f x) = RepresentationTheory.Hecke.RadialDilation.FiniteSchur.Realization.finitePadicProjection p (f y) := by
  have hs : rationalPrimeIdempotent q * f (x - y) = f (x - y) := by
    exact (f.map_smul _ _).symm.trans (congrArg f h)
  have hz := supported_adele_projection_zero q p hpq (f (x - y)) hs
  rw [map_sub, map_sub] at hz
  exact sub_eq_zero.mp hz

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RationalPrimeSupport.TestTransport
