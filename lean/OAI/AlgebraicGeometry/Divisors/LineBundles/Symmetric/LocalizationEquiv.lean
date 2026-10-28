import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationLift
import OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.LocalizedSymmetricExt

/-! # Localization Equiv -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv.BundleCycles

noncomputable section

/-! # LineBundleCycles: the actual symmetric-algebra localization isomorphism -/

variable {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    (D : Submonoid R) (S : Type) [CommRing S] [Algebra R S] [IsLocalization D S]
    {N : Type} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule D f]

attribute [local instance] LocalizationLift.BundleCycles.localizedSymmetricBaseAlgebra

omit [IsLocalizedModule D f] in
theorem symmetricLocalizationMap_scalar (s : S) :
    LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S s) =
      algebraMap S (SymmetricAlgebra S N) s := by
  have h : (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f).comp (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S) =
      algebraMap S (SymmetricAlgebra S N) := by
    apply IsLocalization.ringHom_ext D
    apply RingHom.ext
    intro r
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.localizedSymmetricScalarMap M D S (algebraMap R S r)) = _
    rw [LocalizationLift.BundleCycles.localizedSymmetricScalarMap_algebraMap,
      IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D),
      LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_algebraMap]
    rfl
  exact DFunLike.congr_fun h s

theorem symmetricLocalizationLift_comp_map :
    (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f).comp (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f) =
      RingHom.id (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) := by
  apply IsLocalization.ringHom_ext (LocalizationLift.BundleCycles.symmetricDenominators M D)
  refine ScalarMap.BundleCycles.symmetricRingHom_ext (R := R) (M := M) (T := LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) _ _ ?_ ?_
  · intro r
    change LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f
      (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) (algebraMap R (SymmetricAlgebra R M) r))) = _
    rw [LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_algebraMap,
      LocalizationLift.BundleCycles.symmetricLocalizationLift_algebraMap, LocalizationLift.BundleCycles.localizedSymmetricScalarMap_algebraMap]
    exact IsScalarTower.algebraMap_apply R (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) r
  · intro m
    change LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f
      (algebraMap (SymmetricAlgebra R M) (LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D) (SymmetricAlgebra.ι R M m))) = _
    rw [LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap, LocalizationMap.BundleCycles.symmetricModuleMap_generator,
      LocalizationLift.BundleCycles.symmetricLocalizationLift_generator]
    rfl

theorem symmetricLocalizationMap_comp_lift :
    (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f).comp (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f) =
      RingHom.id (SymmetricAlgebra S N) := by
  apply LocalizedSymmetricExt.BundleCycles.localizedSymmetricRingHom_ext D f
  · intro s
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f
      (algebraMap S (SymmetricAlgebra S N) s)) = _
    rw [LocalizationLift.BundleCycles.symmetricLocalizationLift_algebraMap, symmetricLocalizationMap_scalar]
    rfl
  · intro m
    change LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f
      (SymmetricAlgebra.ι S N (f m))) = _
    rw [LocalizationLift.BundleCycles.symmetricLocalizationLift_generator, LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap,
      LocalizationMap.BundleCycles.symmetricModuleMap_generator]
    rfl

def symmetricLocalizationEquiv : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D ≃+* SymmetricAlgebra S N :=
  RingEquiv.ofRingHom (LocalizationMap.BundleCycles.symmetricLocalizationMap (S := S) D f) (LocalizationLift.BundleCycles.symmetricLocalizationLift M D S f)
    (symmetricLocalizationMap_comp_lift M D S f) (symmetricLocalizationLift_comp_map M D S f)

theorem symmetricModuleMap_isLocalization :
    letI := (LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
    IsLocalization (LocalizationLift.BundleCycles.symmetricDenominators M D) (SymmetricAlgebra S N) := by
  let := (LocalizationMap.BundleCycles.symmetricModuleMap (S := S) f).toAlgebra
  let e : LocalizationLift.BundleCycles.LocalizedSymmetricAlgebra M D ≃ₐ[SymmetricAlgebra R M] SymmetricAlgebra S N := {
    symmetricLocalizationEquiv M D S f with
    commutes' := LocalizationMap.BundleCycles.symmetricLocalizationMap_algebraMap D f
  }
  exact IsLocalization.isLocalization_of_algEquiv (LocalizationLift.BundleCycles.symmetricDenominators M D) e

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Symmetric.LocalizationEquiv.BundleCycles
