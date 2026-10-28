import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationExact
import OAI.AlgebraicGeometry.Divisors.LineBundles.EquationEulerEquiv
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.Module

/-! # Localized Equation Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: localization of the actual multiplication image
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

def localizedEquationRangeEquiv (S : Submonoid R) (x : R) :
    LocalizedModule S (MultiplicationSequence.BundleCycles.equationEndomorphism x M).range ≃ₗ[Localization S]
      (MultiplicationSequence.BundleCycles.equationEndomorphism (algebraMap R (Localization S) x) (LocalizedModule S M)).range := by
  let A := Localization S
  let f := LocalizedModule.mkLinearMap S M
  have he : (IsLocalizedModule.map S f f (MultiplicationSequence.BundleCycles.equationEndomorphism x M)).extendScalarsOfIsLocalization S A =
      MultiplicationSequence.BundleCycles.equationEndomorphism (algebraMap R A x) (LocalizedModule S M) := by
    apply LinearMap.ext
    intro m
    change Periodic.Localization.BundleCycles.localizedEndomorphism S (MultiplicationSequence.BundleCycles.equationEndomorphism x M) m = (algebraMap R A x) • m
    rw [LocalizedEquationExact.BundleCycles.localizedEndomorphism_equation]
    exact (IsScalarTower.algebraMap_smul A x m).symm
  have hr := LinearMap.localized'_range_eq_range_localizedMap A S f f (MultiplicationSequence.BundleCycles.equationEndomorphism x M)
  rw [he] at hr
  exact ((MultiplicationSequence.BundleCycles.equationEndomorphism x M).range.localizedEquiv S).symm.trans (LinearEquiv.ofEq _ _ hr)

def equationRangeEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (x : R) (e : M ≃ₗ[R] N) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism x M).range ≃ₗ[R] (MultiplicationSequence.BundleCycles.equationEndomorphism x N).range :=
  e.ofSubmodules _ _ (EquationEulerEquiv.BundleCycles.equationRange_map_equiv x e)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedEquationImage.BundleCycles
