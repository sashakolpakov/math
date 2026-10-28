import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleComposition

/-! # Open Over Coherence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenOverCoherence

noncomputable section

/-! Comparison diagrams for native restriction and the equivalent over-site. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem overRestriction_comparison {X : Scheme.{u}} {U V : X.Opens}
    (h : V ≤ U) (M : X.Modules) :
    ((Scheme.Modules.overFunctorEquiv V).app M).inv ≫
      (Scheme.Modules.overEquiv V).functor.map
        (( _root_.SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)).inv.app M) ≫
      (Scheme.Modules.overMapCompOverEquiv (homOfLE h)).hom.app (M.over U) =
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M ≫
      (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).hom.app M ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        ((Scheme.Modules.overFunctorEquiv U).app M).inv := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h₁ : (X.homOfLE h ≫ U.ι) ''ᵁ W.unop = V.ι ''ᵁ W.unop := by
    simp only [X.homOfLE_ι h]
  have h₂ : U.ι ''ᵁ ((X.homOfLE h) ''ᵁ W.unop) =
      (X.homOfLE h ≫ U.ι) ''ᵁ W.unop := by
    rw [Scheme.Hom.comp_image]
  change M.presheaf.map (eqToHom (h₂.trans h₁)).op x =
    M.presheaf.map (eqToHom h₂).op (M.presheaf.map (eqToHom h₁).op x)
  rw [← M.presheaf.map_comp_apply]
  congr 1

theorem overRestriction_unit {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    (Scheme.Modules.overMapCompOverEquiv (homOfLE h)).hom.app
        (_root_.SheafOfModules.unit (X.ringCatSheaf.over U)) ≫
      (Scheme.Modules.restrictFunctor (X.homOfLE h)).map
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
      (Scheme.Modules.restrictUnitIso (X.homOfLE h)).hom =
    (Scheme.Modules.overEquiv V).functor.map
        (_root_.SheafOfModules.overMapUnitIso (homOfLE h)).hom ≫
      (V.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom := by
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hWV : U.ι ''ᵁ ((X.homOfLE h) ''ᵁ W.unop) = V.ι ''ᵁ W.unop := by
    simp only [← Scheme.Hom.comp_image, X.homOfLE_ι h]
  change ((X.homOfLE h).appIso W.unop).hom
    (X.presheaf.map (eqToHom hWV).op x) = x
  have hi := ConcreteCategory.congr_hom
    (Scheme.Hom.appIso_homOfLE_inv h W.unop) x
  change ((X.homOfLE h).appIso W.unop).inv x =
    X.presheaf.map (eqToHom hWV).op x at hi
  rw [← hi]
  exact ConcreteCategory.congr_hom
    ((X.homOfLE h).appIso W.unop).inv_hom_id x

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenOverCoherence
