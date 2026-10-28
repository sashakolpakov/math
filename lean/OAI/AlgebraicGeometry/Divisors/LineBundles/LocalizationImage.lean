import OAI.AlgebraicGeometry.Divisors.LineBundles.MultiplicationSequence
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Localization Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual image of a module in its localization

This is the branch module used in the periodic reciprocity argument.
It remains finite over the original ring, and every denominator acts
injectively on it. Localizing it again recovers the original localization.
-/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

abbrev localizationImage (S : Submonoid R) (M : Type*) [AddCommGroup M] [Module R M] :=
  (LocalizedModule.mkLinearMap S M).range

def localizationImageProjection (S : Submonoid R) : M →ₗ[R] localizationImage S M :=
  (LocalizedModule.mkLinearMap S M).rangeRestrict

theorem localizationImageProjection_surjective (S : Submonoid R) :
    Function.Surjective (localizationImageProjection (M := M) S) :=
  LinearMap.surjective_rangeRestrict _

instance localizationImage_finite (S : Submonoid R) [Module.Finite R M] :
    Module.Finite R (localizationImage S M) :=
  Module.Finite.range _

theorem localizationImage_equation_injective (S : Submonoid R) (x : S) :
    Function.Injective (MultiplicationSequence.BundleCycles.equationEndomorphism (x : R) (localizationImage S M)) := by
  intro m n h
  apply Subtype.ext
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap S M) x
  exact congrArg (fun z : localizationImage S M => (z : LocalizedModule S M)) h

instance localizationImage_isLocalized (S : Submonoid R) :
    IsLocalizedModule S (localizationImage S M).subtype where
  map_units := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap S M)
  surj m := by
    obtain ⟨⟨n, s⟩, h⟩ := IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S M) m
    exact ⟨⟨localizationImageProjection S n, s⟩, h⟩
  exists_of_eq h := by
    exact ⟨1, by simpa only [one_smul] using Subtype.ext h⟩

def localizationImageLocalEquiv (S : Submonoid R) :
    LocalizedModule S (localizationImage S M) ≃ₗ[R] LocalizedModule S M :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (localizationImage S M))
    (localizationImage S M).subtype

theorem localizationImage_equation_comp_zero (S : Submonoid R) (a b : R)
    (h : (MultiplicationSequence.BundleCycles.equationEndomorphism b M).comp (MultiplicationSequence.BundleCycles.equationEndomorphism a M) = 0) :
    (MultiplicationSequence.BundleCycles.equationEndomorphism b (localizationImage S M)).comp
      (MultiplicationSequence.BundleCycles.equationEndomorphism a (localizationImage S M)) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨m, rfl⟩ := localizationImageProjection_surjective S x
  let f := localizationImageProjection (M := M) S
  change b • (a • f m) = 0
  rw [← f.map_smul, ← f.map_smul]
  exact (congrArg f (LinearMap.congr_fun h m)).trans f.map_zero

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizationImage.BundleCycles
