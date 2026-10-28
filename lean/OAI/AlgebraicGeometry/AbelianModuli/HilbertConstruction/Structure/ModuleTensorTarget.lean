import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardStructureComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits

/-! # Module Tensor Target -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorTarget

noncomputable section

/-! The target of the structure-module tensor comparison identifies with ordinary functions on inverse-image opens, and its unit section map is the actual pullback of regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R] (a : Y ⟶ X) (f : R →+* Γ(X, ⊤))

def baseChangedStructureModuleSectionsIso :
    Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj (Line.Bundles.structureModule X))) ≅
        Tensor.SectionModules.inverseImageSectionModules a f :=
  (Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor f).mapIso ((Scheme.Modules.pushforward a).mapIso (Line.Bundles.structureModulePullbackIso a)) ≪≫
    Coefficient.PushforwardStructureComparison.coefficientPushforwardStructureIso a f

theorem baseChangedStructureModuleSectionsIso_apply (U : X.Opens)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj (Line.Bundles.structureModule X)))).obj (.op U)) :
    (baseChangedStructureModuleSectionsIso a f).hom.app (.op U) x =
      (Line.Bundles.structureModulePullbackIso a).hom.app (a ⁻¹ᵁ U) x := rfl

theorem baseChangedStructureModuleSectionsIso_unit (U : X.Opens)
    (r : (Coefficient.ModulePresheaf.coefficientModulePresheaf f (Line.Bundles.structureModule X)).obj (.op U)) :
    (baseChangedStructureModuleSectionsIso a f).hom.app (.op U)
      ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap a f (Line.Bundles.structureModule X)).app (.op U) r) = a.app U r :=
  congrArg (fun z : Line.Bundles.structureModule X ⟶ (Scheme.Modules.pushforward a).obj (Line.Bundles.structureModule Y) => z.app U r)
    (Tensor.PullbackUnits.structureModulePullbackIso_unit a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.ModuleTensorTarget
