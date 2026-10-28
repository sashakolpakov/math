import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalBasicOpenLocalization

/-! # Base Section Localization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseSectionLocalization

noncomputable section

/-! Global-section localization over the actual coefficient ring of a
base scheme, including the canonical direct-image section maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u v

theorem moduleCat_isLocalized_restrictScalars
    {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A) (r : R)
    {M N : ModuleCat.{v} A} (a : M ⟶ N)
    [IsLocalizedModule.Away (φ r) a.hom] :
    IsLocalizedModule.Away r ((ModuleCat.restrictScalars φ).map a).hom := by
  let : Algebra R A := φ.toAlgebra
  let : Module R M := Module.compHom M φ
  let : Module R N := Module.compHom N φ
  let : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact IsLocalizedModule.restrictScalars_powers r a.hom

theorem baseGlobalBasicOpen_isLocalized
    {X B : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (f : X ⟶ B) (M : X.Modules) [M.IsQuasicoherent] (r : Γ(B, ⊤)) :
    IsLocalizedModule.Away r
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).map (X.basicOpen (f.appTop r)).leTop.op).hom := by
  let a := (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) M).map (X.basicOpen (f.appTop r)).leTop.op
  have : IsLocalizedModule.Away (f.appTop r) a.hom := GlobalBasicOpenLocalization.globalBasicOpen_isLocalized M _
  exact moduleCat_isLocalized_restrictScalars f.appTop.hom r a

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseSectionLocalization
