import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor

/-! # Pullback Section Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap

noncomputable section

/-! The pullback adjunction gives the actual coefficient-linear section maps on every open set, naturally in the module sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : Y ⟶ X) (f : R →+* Γ(X, ⊤))

def coefficientPullbackSectionPresheafMap (M : X.Modules) :
    ModulePresheaf.coefficientModulePresheaf f M ⟶
      ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj M)) :=
  (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)

theorem coefficientPullbackSectionPresheafMap_natural {M N : X.Modules} (b : M ⟶ N) :
    (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map b ≫ coefficientPullbackSectionPresheafMap a f N =
      coefficientPullbackSectionPresheafMap a f M ≫
        (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
          ((Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map b)) := by
  unfold coefficientPullbackSectionPresheafMap
  exact ((ModulePresheafFunctor.coefficientModulePresheafFunctor f).map_comp b
    ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app N)).symm.trans
      ((congrArg ((ModulePresheafFunctor.coefficientModulePresheafFunctor f).map)
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.naturality b)).trans
        ((ModulePresheafFunctor.coefficientModulePresheafFunctor f).map_comp
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M)
          ((Scheme.Modules.pushforward a).map ((Scheme.Modules.pullback a).map b))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap
