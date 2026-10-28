import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSection
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.RestrictedPullback

/-! # Base Section Pullback Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction

noncomputable section

/-! Restricted actual section pullback is semilinear for scalars from
the base of a commuting square. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

namespace Construction

universe u

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
  (h : f ≫ π = ρ ≫ g) (M : X.Modules) (U : X.Opens) (V : Y.Opens) (hV : V ≤ f ⁻¹ᵁ U)

def restrictedBaseSectionPullback : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) ⟶
    (ModuleCat.restrictScalars g.appTop.hom).obj
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op V)) :=
  Quotients.FiniteDescent.BaseSection.Construction.BaseSectionPullback.map f π ρ g h M U ≫
    (ModuleCat.restrictScalars g.appTop.hom).map
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).map (homOfLE hV).op)

theorem restrictedBaseSectionPullback_apply (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    restrictedBaseSectionPullback f π ρ g h M U V hV s = Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hV s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op
    (Quotients.FiniteDescent.BaseSection.Construction.BaseSectionPullback.map f π ρ g h M U s) = _
  rw [Quotients.FiniteDescent.BaseSection.Construction.BaseSectionPullback.map_apply]
  rfl

include h in
theorem restrictedBaseSectionPullback_smul (r : Γ(S, ⊤))
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hV (r • s) =
      @SMul.smul Γ(T, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op V))
        inferInstance (g.appTop r) (Quotients.FiniteDescent.RestrictedPullback.Construction.RestrictedPullbackSections.map f M U V hV s) := by
  have he := (restrictedBaseSectionPullback f π ρ g h M U V hV).hom.map_smul r s
  change restrictedBaseSectionPullback f π ρ g h M U V hV (r • s) =
    @SMul.smul Γ(T, ⊤) ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op V))
      inferInstance (g.appTop r) (restrictedBaseSectionPullback f π ρ g h M U V hV s) at he
  simpa only [restrictedBaseSectionPullback_apply] using he

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.BaseSectionPullbackRestriction
