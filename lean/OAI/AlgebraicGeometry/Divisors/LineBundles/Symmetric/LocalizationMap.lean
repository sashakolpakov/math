import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift

/-! # Localization Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual map from localized symmetric polynomials to localized-module polynomials -/

variable {R S M N : Type} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]

def scalarExtensionSemilinear (f : M →ₗ[R] N) : M →ₛₗ[algebraMap R S] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r m := by rw [f.map_smul, algebraMap_smul]

def symmetricModuleMap (f : M →ₗ[R] N) : SymmetricAlgebra R M →+* SymmetricAlgebra S N :=
  ScalarMap.BundleCycles.symmetricScalarMap (algebraMap R S) (scalarExtensionSemilinear f)

theorem symmetricModuleMap_generator (f : M →ₗ[R] N) (m : M) :
    symmetricModuleMap (S := S) f (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι S N (f m) :=
  ScalarMap.BundleCycles.symmetricScalarMap_generator _ _ _

theorem symmetricModuleMap_algebraMap (f : M →ₗ[R] N) (r : R) :
    symmetricModuleMap (S := S) f (algebraMap R (SymmetricAlgebra R M) r) =
      algebraMap S (SymmetricAlgebra S N) (algebraMap R S r) :=
  ScalarMap.BundleCycles.symmetricScalarMap_algebraMap _ _ _

variable (D : Submonoid R) [IsLocalization D S] (f : M →ₗ[R] N)

theorem symmetricModuleMap_units (d : LocalizationLift.BundleCycles.symmetricDenominators M D) :
    IsUnit (symmetricModuleMap (S := S) f d.val) := by
  obtain ⟨r, hr, he⟩ := d.property
  change algebraMap R (SymmetricAlgebra R M) r = d.val at he
  rw [← he, symmetricModuleMap_algebraMap]
  exact (IsLocalization.map_units S (⟨r, hr⟩ : D)).map (algebraMap S (SymmetricAlgebra S N))

def symmetricLocalizationMap : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D →+* SymmetricAlgebra S N :=
  IsLocalization.lift (symmetricModuleMap_units D f)

theorem symmetricLocalizationMap_algebraMap (a : SymmetricAlgebra R M) :
    symmetricLocalizationMap (S := S) D f (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) a) =
      symmetricModuleMap (S := S) f a :=
  IsLocalization.lift_eq (symmetricModuleMap_units D f) a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap.BundleCycles
