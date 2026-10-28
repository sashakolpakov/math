import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.ScalarMap
import Mathlib.RingTheory.Localization.Module

/-! # Localization Lift -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual scalar maps into the localization of a symmetric algebra -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R)

def symmetricDenominators : Submonoid (SymmetricAlgebra R M) :=
  D.map (algebraMap R (SymmetricAlgebra R M))

abbrev LocalizedSymmetricAlgebra := Localization (symmetricDenominators M D)

abbrev localizedSymmetricBaseAlgebra : Algebra R (LocalizedSymmetricAlgebra M D) :=
  inferInstance

attribute [local instance] localizedSymmetricBaseAlgebra

instance localizedSymmetricBase_tower : IsScalarTower R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) :=
  inferInstance

theorem localizedSymmetricScalar_units (d : D) :
    IsUnit (algebraMap R (LocalizedSymmetricAlgebra M D) d.val) := by
  let d' : symmetricDenominators M D :=
    ⟨algebraMap R (SymmetricAlgebra R M) d.val, Submonoid.mem_map_of_mem _ d.property⟩
  rw [IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D)]
  exact IsLocalization.map_units (LocalizedSymmetricAlgebra M D) d'

variable (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]

def localizedSymmetricScalarMap : S →+* LocalizedSymmetricAlgebra M D :=
  IsLocalization.lift (localizedSymmetricScalar_units M D)

theorem localizedSymmetricScalarMap_algebraMap (r : R) :
    localizedSymmetricScalarMap M D S (algebraMap R S r) =
      algebraMap R (LocalizedSymmetricAlgebra M D) r :=
  IsLocalization.lift_eq (localizedSymmetricScalar_units M D) r

abbrev localizedSymmetricAlgebra : Algebra S (LocalizedSymmetricAlgebra M D) :=
  (localizedSymmetricScalarMap M D S).toAlgebra

attribute [local instance] localizedSymmetricAlgebra

instance localizedSymmetricScalar_tower : IsScalarTower R S (LocalizedSymmetricAlgebra M D) :=
  IsScalarTower.of_algebraMap_eq fun r => (localizedSymmetricScalarMap_algebraMap M D S r).symm

def localizedSymmetricGenerator : M →ₗ[R] LocalizedSymmetricAlgebra M D :=
  (IsScalarTower.toAlgHom R (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D)).toLinearMap.comp
    (SymmetricAlgebra.ι R M)

theorem localizedSymmetricGenerator_units (d : D) :
    IsUnit (algebraMap R (Module.End R (LocalizedSymmetricAlgebra M D)) d.val) := by
  apply (Module.End.isUnit_iff _).mpr
  have h : Function.Bijective (fun x : LocalizedSymmetricAlgebra M D =>
      algebraMap R (LocalizedSymmetricAlgebra M D) d.val • x) :=
    (localizedSymmetricScalar_units M D d).smul_bijective
  change Function.Bijective (fun x : LocalizedSymmetricAlgebra M D => d.val • x)
  have he : (fun x : LocalizedSymmetricAlgebra M D =>
      algebraMap R (LocalizedSymmetricAlgebra M D) d.val • x) = (fun x => d.val • x) := by
    funext x
    change algebraMap R (LocalizedSymmetricAlgebra M D) d.val * x = d.val • x
    exact (Algebra.smul_def d.val x).symm
  exact he ▸ h

end

/-! # LineBundleCycles: the actual inverse map from the symmetric algebra of a localized module -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R) (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]
    {N : Type} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

attribute [local instance] localizedSymmetricBaseAlgebra localizedSymmetricAlgebra

def symmetricLocalizationLiftLinear : N →ₗ[S] LocalizedSymmetricAlgebra M D :=
  (IsLocalizedModule.lift D f (localizedSymmetricGenerator M D)
    (localizedSymmetricGenerator_units M D)).extendScalarsOfIsLocalization D S

theorem symmetricLocalizationLiftLinear_apply (m : M) :
    symmetricLocalizationLiftLinear M D S f (f m) =
      algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m) :=
  IsLocalizedModule.lift_apply D f (localizedSymmetricGenerator M D)
    (localizedSymmetricGenerator_units M D) m

def symmetricLocalizationLiftData :
    {g : SymmetricAlgebra S N →+* LocalizedSymmetricAlgebra M D //
      (∀ m, g (SymmetricAlgebra.ι S N (f m)) =
        algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m)) ∧
      ∀ s, g (algebraMap S (SymmetricAlgebra S N) s) = localizedSymmetricScalarMap M D S s} := by
  let e := @Extension.BundleCycles.symmetricExtension S N (LocalizedSymmetricAlgebra M D) (by infer_instance)
    (by infer_instance) (by infer_instance) (by infer_instance) (localizedSymmetricAlgebra M D S)
    (symmetricLocalizationLiftLinear M D S f)
  refine ⟨e.val, ?_, e.property.2⟩
  intro m
  exact (e.property.1 (f m)).trans (symmetricLocalizationLiftLinear_apply M D S f m)

def symmetricLocalizationLift : SymmetricAlgebra S N →+* LocalizedSymmetricAlgebra M D :=
  (symmetricLocalizationLiftData M D S f).val

theorem symmetricLocalizationLift_generator (m : M) :
    symmetricLocalizationLift M D S f (SymmetricAlgebra.ι S N (f m)) =
      algebraMap (SymmetricAlgebra R M) (LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m) :=
  (symmetricLocalizationLiftData M D S f).property.1 m

theorem symmetricLocalizationLift_algebraMap (s : S) :
    symmetricLocalizationLift M D S f (algebraMap S (SymmetricAlgebra S N) s) =
      localizedSymmetricScalarMap M D S s :=
  (symmetricLocalizationLiftData M D S f).property.2 s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift.BundleCycles
