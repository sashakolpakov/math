import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechPullbackHomology
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseModule

/-! # Module Sections -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleSections

noncomputable section

/-! Pullback of module sections along a morphism over a fixed base, with
restriction to an arbitrary smaller open on the source. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

namespace Construction.ModuleSectionsOver

variable {X Y S : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ S)
variable (h : f ≫ π = ρ) (M : X.Modules)

def preimageMap (U : X.Opens) : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) ⟶
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U)) :=
  ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).app (op U) ≫
  (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso f π ((Scheme.Modules.pullback f).obj M) U).inv ≫
  eqToHom (congrArg (fun p =>
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U))) h)

theorem preimageMap_apply (U : X.Opens) (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    preimageMap f π ρ h M U s = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  subst ρ
  rfl

def map (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) ⟶
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op V) :=
  preimageMap f π ρ h M U ≫
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).map (homOfLE hVU).op

theorem map_apply (U : X.Opens) (V : Y.Opens) (hVU : V ≤ f ⁻¹ᵁ U)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    ModuleSectionsOver.map f π ρ h M U V hVU s = ((Scheme.Modules.pullback f).obj M).presheaf.map
      (homOfLE hVU).op (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s) := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hVU).op
    (preimageMap f π ρ h M U s) = _
  rw [preimageMap_apply]

theorem restrict {U U' : X.Opens} {V V' : Y.Opens}
    (i : U' ⟶ U) (j : V' ⟶ V) (hVU : V ≤ f ⁻¹ᵁ U) (hV'U' : V' ≤ f ⁻¹ᵁ U')
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    ModuleSectionsOver.map f π ρ h M U' V' hV'U' ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).map i.op s) =
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).map j.op
        (ModuleSectionsOver.map f π ρ h M U V hVU s) := by
  rw [map_apply, map_apply]
  change ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV'U').op
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U' (M.presheaf.map i.op s)) =
    ((Scheme.Modules.pullback f).obj M).presheaf.map j.op
      (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hVU).op
        (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s))
  rw [show i = homOfLE (leOfHom i) from Subsingleton.elim _ _]
  rw [PullbackSectionRestrict.Construction.PullbackSectionCoefficients.restrict f M (leOfHom i)]
  rw [← ((Scheme.Modules.pullback f).obj M).presheaf.map_comp_apply,
    ← ((Scheme.Modules.pullback f).obj M).presheaf.map_comp_apply]
  rfl

end Construction.ModuleSectionsOver

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ModuleSections
