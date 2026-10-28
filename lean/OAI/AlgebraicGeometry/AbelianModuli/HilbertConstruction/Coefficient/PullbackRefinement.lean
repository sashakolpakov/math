import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.RefinementOpenValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap

/-! # Pullback Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackRefinement

noncomputable section

/-! Refinement of a pullback gives a coefficient-linear map on section presheaves, invertible on opens covered by an open refinement. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : X ⟶ Y) (g : Y ⟶ Z) (f : R →+* Γ(Z, ⊤)) (M : Z.Modules)

def coefficientPullbackRefinementMap :
    ModulePresheaf.coefficientModulePresheaf f ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M)) ⟶
      ModulePresheaf.coefficientModulePresheaf f
        ((Scheme.Modules.pushforward (a ≫ g)).obj ((Scheme.Modules.pullback (a ≫ g)).obj M)) :=
  (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map (OpenPullback.Refinement.openPullbackRefinementMap a g M)

theorem coefficientPullbackRefinementMap_apply (U : Z.Opens)
    (x : (ModulePresheaf.coefficientModulePresheaf f
      ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pullback g).obj M))).obj (.op U)) :
    (coefficientPullbackRefinementMap a g f M).app (.op U) x =
      ((Scheme.Modules.pullbackComp a g).hom.app M).app ((a ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback g).obj M)).app
          (g ⁻¹ᵁ U) x) := rfl

theorem coefficientPullbackRefinementMap_app_isIso [IsOpenImmersion a]
    (U : Z.Opens) (hU : g ⁻¹ᵁ U ≤ a.opensRange) :
    IsIso ((coefficientPullbackRefinementMap a g f M).app (.op U)) := by
  have := Pullback.RefinementOpenValues.pullbackRefinementMap_app_isIso_of_preimage a g M U hU
  exact Pullback.RefinementOpenValues.coefficientModulePresheafMap_app_isIso f (OpenPullback.Refinement.openPullbackRefinementMap a g M) U

theorem pullbackCoefficient_compatible_comp {B : Type u} [CommRing B] [Algebra R B]
    (q : B →+* Γ(Y, ⊤)) (hq : q.comp (algebraMap R B) = g.appTop.hom.comp f) :
    (a.appTop.hom.comp q).comp (algebraMap R B) = (a ≫ g).appTop.hom.comp f := by
  ext r
  change a.appTop (q (algebraMap R B r)) = (a ≫ g).appTop (f r)
  rw [show q (algebraMap R B r) = g.appTop (f r) from DFunLike.congr_fun hq r]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackRefinement
