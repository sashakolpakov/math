import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.PrimeFiltration
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalSurfaceOrderSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports

/-! # Prime Equation Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeEquationOrder

noncomputable section

/-! A generator of a prime divisor ideal has order one on that divisor
and zero on every other divisor through the point where it is an equation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

universe u

theorem localized (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p q : PrimeSpectrum R) (hp : p.asIdeal ≠ ⊥) (hq : q.asIdeal.height = 1)
    (r : R) (he : p.asIdeal = Ideal.span {r}) :
    Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap R (Localization.AtPrime q.asIdeal) r) =
      if p = q then 1 else 0 := by
  let e : QuotSMulTop r R ≃ₗ[R] R ⧸ p.asIdeal :=
    (NormalSurfaceOrderSum.principalQuotientEquiv R r).trans (Submodule.quotEquivOfEq _ _ he.symm)
  rw [← Principal.PrimeFiltration.localized_principal_length R r q,
    FiltrationBaseLength.length_iso R (Localization.AtPrime q.asIdeal) e.toModuleIso]
  exact PrimeFiltrationMultiplicity.localized_prime_length R q p hq hp

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient

theorem geometric (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (D B : X.DimensionCycleSupport 1) (x : X.carrier)
    (hxD : x ∈ (D.val : Set X.carrier)) (hxB : x ∈ (B.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk x) (hr : r ≠ 0)
    (he : RingHom.ker (Local.Principal.supportStalkMap X.carrier D.val x hxD).hom = Ideal.span {r}) :
    X.carrier.ord (algebraMap (X.carrier.presheaf.stalk x) X.carrier.functionField r)
      (CycleClass.Thom.IntersectionGeometry.supportPoint B.val) = if B = D then 1 else 0 := by
  let p := Stalk.PrimeQuotient.kernelPrime X.carrier D.val x hxD
  let q := Stalk.PrimeQuotient.kernelPrime X.carrier B.val x hxB
  have hp : p.asIdeal.height = 1 := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact CurveSupports.coheight_one X m D
  have hq : q.asIdeal.height = 1 := by
    rw [Stalk.Localization.height_eq_coheight_image, Stalk.PrimeQuotient.kernelPrime_image]
    exact CurveSupports.coheight_one X m B
  have hp₀ : p.asIdeal ≠ ⊥ := by
    intro hz
    rw [hz, Ideal.height_bot] at hp
    exact zero_ne_one hp
  have hpq : p = q ↔ B = D := by
    constructor
    · intro h
      apply Subtype.ext
      apply irreducibleSetEquivPoints.injective
      exact (Stalk.PrimeQuotient.kernelPrime_image X.carrier B.val x hxB).symm.trans
        ((congrArg (X.carrier.fromSpecStalk x) h.symm).trans (Stalk.PrimeQuotient.kernelPrime_image X.carrier D.val x hxD))
    · intro h
      subst B
      rfl
  have ho := Stalk.DivisorRestriction.order_of_local_element X.carrier x r hr q hq
  rw [Stalk.PrimeQuotient.kernelPrime_image, localized (X.carrier.presheaf.stalk x) p q hp₀ hq r he, hpq] at ho
  simpa only [apply_ite, ENat.toNat_one, ENat.toNat_zero, Nat.cast_one, Nat.cast_zero] using ho

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeEquationOrder
