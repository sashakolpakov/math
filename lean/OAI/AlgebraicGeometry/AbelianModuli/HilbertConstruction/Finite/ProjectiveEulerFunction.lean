import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-! # Projective Euler Function -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveEulerFunction

noncomputable section

/-! The alternating rank sum of finitely many finite projective terms is locally constant on the base spectrum. -/
open _root_.CategoryTheory
universe u

def finiteProjectiveEulerAt {R : Type u} [CommRing R]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ) (p : PrimeSpectrum R) : ℤ :=
  ∑ q ∈ Finset.range N, (-1 : ℤ) ^ q * (Module.rankAtStalk (D.X q) p : ℤ)

theorem finiteProjectiveEulerAt_isLocallyConstant {R : Type u} [CommRing R]
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q)) :
    IsLocallyConstant (finiteProjectiveEulerAt D N) := by
  have hterm (q : ℕ) : IsLocallyConstant
      (fun p : PrimeSpectrum R => (-1 : ℤ) ^ q * (Module.rankAtStalk (D.X q) p : ℤ)) := by
    have := hfinite q
    have := hprojective q
    have : Module.FinitePresentation R (D.X q) := Module.finitePresentation_of_projective R _
    exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := D.X q)).comp
      (fun r : ℕ => (-1 : ℤ) ^ q * (r : ℤ))
  have hsum (s : Finset ℕ) : IsLocallyConstant
      (fun p : PrimeSpectrum R => ∑ q ∈ s, (-1 : ℤ) ^ q * (Module.rankAtStalk (D.X q) p : ℤ)) := by
    induction s using Finset.induction_on with
    | empty =>
        have he : (fun p : PrimeSpectrum R => ∑ q ∈ (∅ : Finset ℕ),
            (-1 : ℤ) ^ q * (Module.rankAtStalk (D.X q) p : ℤ)) = Function.const (PrimeSpectrum R) 0 := by
          funext p
          exact Finset.sum_empty
        exact (congrArg (fun f : PrimeSpectrum R → ℤ => IsLocallyConstant f) he).mpr
          (IsLocallyConstant.const 0)
    | @insert q s hq ih =>
        have he : (fun p : PrimeSpectrum R => ∑ j ∈ insert q s,
            (-1 : ℤ) ^ j * (Module.rankAtStalk (D.X j) p : ℤ)) =
            (fun p => (-1 : ℤ) ^ q * (Module.rankAtStalk (D.X q) p : ℤ)) +
              (fun p => ∑ j ∈ s, (-1 : ℤ) ^ j * (Module.rankAtStalk (D.X j) p : ℤ)) := by
          funext p
          exact Finset.sum_insert hq
        exact (congrArg (fun f : PrimeSpectrum R → ℤ => IsLocallyConstant f) he).mpr ((hterm q).add ih)
  exact hsum (Finset.range N)

theorem finiteProjectiveEulerAt_eq_of_preconnected {R : Type u} [CommRing R]
    [PreconnectedSpace (PrimeSpectrum R)] (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q))
    (p q : PrimeSpectrum R) : finiteProjectiveEulerAt D N p = finiteProjectiveEulerAt D N q :=
  (finiteProjectiveEulerAt_isLocallyConstant D N hfinite hprojective).apply_eq_of_preconnectedSpace p q

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveEulerFunction
