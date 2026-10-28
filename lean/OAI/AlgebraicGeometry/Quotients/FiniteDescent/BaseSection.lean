import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CechBaseTmul
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionRestrict

/-! # Base Section -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSection

noncomputable section

/-! The canonical pullback on sections with scalar actions from a commuting base square. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry.Scheme.Modules
open scoped ChangeOfRings

universe u

namespace Construction.BaseSectionPullback

variable {X Y S T : Scheme.{u}} (f : Y ⟶ X) (π : X ⟶ S) (ρ : Y ⟶ T) (g : T ⟶ S)
variable (h : f ≫ π = ρ ≫ g) (M : X.Modules) (U : X.Opens)

def map : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U) ⟶
    (ModuleCat.restrictScalars g.appTop.hom).obj
      ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U))) :=
  ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheafFunctor π).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).app (op U) ≫
  (SheafCohomology.Projective.OrderedBaseCechPushforward.Scheme.Modules.baseModulePresheafPushforwardAppIso f π ((Scheme.Modules.pullback f).obj M) U).inv ≫
  eqToHom (congrArg (fun p =>
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U))) h) ≫
  (BaseScalar.Construction.BaseScalarRestriction.sectionsIso ρ g ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)).hom

private theorem eq_apply {Y S : Scheme.{u}} {p q : Y ⟶ S} (h : p = q)
    (M : Y.Modules) (U : Y.Opens) (x : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p M).obj (op U)) :
    eqToHom (congrArg (fun p => (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf p M).obj (op U)) h) x = x := by
  cases h
  rfl

theorem map_apply (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    BaseSectionPullback.map f π ρ g h M U s = PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  exact eq_apply h ((Scheme.Modules.pullback f).obj M) (f ⁻¹ᵁ U)
    (PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s)

def tensorMap :
    (ModuleCat.extendScalars g.appTop.hom).obj ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) ⟶
      (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf ρ ((Scheme.Modules.pullback f).obj M)).obj (op (f ⁻¹ᵁ U)) :=
  ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).symm
    (BaseSectionPullback.map f π ρ g h M U)

theorem tensorMap_one_tmul (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf π M).obj (op U)) :
    tensorMap f π ρ g h M U ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] s) =
      PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M U s := by
  have he := ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).apply_symm_apply
    (BaseSectionPullback.map f π ρ g h M U)
  exact (ConcreteCategory.congr_hom he s).trans (map_apply f π ρ g h M U s)

end Construction.BaseSectionPullback

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BaseSection
