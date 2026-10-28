import OAI.AlgebraicGeometry.Divisors.LineBundles.PrimeIntersectionLength

/-! # Localized Equation Length -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationLength.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localized equation multiplicities in actual quotient rings

The localization of R/bR is canonically R_P/bR_P. This identifies the
module length appearing in the prime-filtration formula with the actual
local quotient length defining the divisor multiplicity.
-/

variable {R : Type*} [CommRing R]

def localizedIdealQuotientEquiv (S : Submonoid R) (J : Ideal R) :
    LocalizedModule S (R ⧸ J) ≃ₗ[Localization S]
      (Localization S) ⧸ J.map (algebraMap R (Localization S)) := by
  let A := Localization S
  let L := J.localized' A S (Algebra.linearMap R A)
  have hL : L = J.map (algebraMap R A) := by
    dsimp only [L]
    rw [Submodule.localized'_eq_span]
    rfl
  let e : LocalizedModule S (R ⧸ J) ≃ₗ[R] A ⧸ L :=
    IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap _ _)
      (J.toLocalizedQuotient' A S (Algebra.linearMap R A))
  exact (e.extendScalarsOfIsLocalization S A).trans (Submodule.quotEquivOfEq _ _ hL)

def localizedEquationCokernelEquiv (S : Submonoid R) (b : R) :
    LocalizedModule S (MultiplicationSequence.BundleCycles.equationCokernel b R) ≃ₗ[Localization S]
      (Localization S) ⧸ Ideal.span {algebraMap R (Localization S) b} := by
  have h : (Ideal.span {b}).map (algebraMap R (Localization S)) =
      Ideal.span {algebraMap R (Localization S) b} := by
    rw [Ideal.map_span, Set.image_singleton]
  exact (LocalizedFiltrationLength.BundleCycles.localizedModuleEquiv S
    (Submodule.quotEquivOfEq _ _ (LocalIntersectionLength.BundleCycles.equationEndomorphism_range_eq_span b))).trans
      ((localizedIdealQuotientEquiv S (Ideal.span {b})).trans (Submodule.quotEquivOfEq _ _ h))

/-- The actual length of the equation quotient at the specified prime. -/
def primeEquationMultiplicity (b : R) (P : Ideal R) (hP : P.IsPrime) : ℕ :=
  letI : P.IsPrime := hP
  (Module.length (Localization P.primeCompl)
    ((Localization P.primeCompl) ⧸ Ideal.span {algebraMap R (Localization P.primeCompl) b})).toNat

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationLength.BundleCycles
