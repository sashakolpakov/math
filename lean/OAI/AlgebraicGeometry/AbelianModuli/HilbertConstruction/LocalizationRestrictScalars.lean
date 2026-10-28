import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-! # Localization Restrict Scalars -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationRestrictScalars

noncomputable section

/-! Localization of sections is compatible with restriction of the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem moduleCat_localization_restrictScalars
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (r : R)
    {M N : ModuleCat.{u} A} (a : M ⟶ N) [IsLocalizedModule.Away (φ r) a.hom] :
    IsLocalizedModule.Away r ((ModuleCat.restrictScalars φ).map a).hom := by
  let : Algebra R A := φ.toAlgebra
  let : Module R M := Module.compHom M φ
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact IsLocalizedModule.restrictScalars_powers r a.hom

theorem coefficientSection_localization_restrictScalars
    {X : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) (c : A →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (r : R)
    [IsLocalizedModule.Away (φ r) ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map U.leTop.op).hom] :
    IsLocalizedModule.Away r ((Coefficient.ModulePresheaf.coefficientModulePresheaf (c.comp φ) M).map U.leTop.op).hom :=
  moduleCat_localization_restrictScalars φ r ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map U.leTop.op)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationRestrictScalars
