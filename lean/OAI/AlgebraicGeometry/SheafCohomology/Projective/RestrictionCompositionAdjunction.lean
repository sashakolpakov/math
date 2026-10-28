import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackCompositionMate
import OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleComposition

/-! # Restriction Composition Adjunction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionCompositionAdjunction

/-! Coherence of restriction composition, proved through the adjunction units. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem restrictionComp_unit {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) :
    (Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map
        ((Scheme.Modules.restrictFunctorComp f g).hom.app M) =
    ((Scheme.Modules.restrictAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)).unit.app M ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.restrictFunctor g ⋙ Scheme.Modules.restrictFunctor f).obj M) := by
  rw [Adjunction.comp_unit_app]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleComposition.module_comp_apply]
  conv_rhs => rw [ModuleComposition.module_comp_apply]
  change ((Scheme.Modules.restrictFunctorComp f g).hom.app M).app
      ((f ≫ g) ⁻¹ᵁ U.unop)
      (((Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M).app U.unop x) =
    (((Scheme.Modules.restrictAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map
        ((Scheme.Modules.restrictAdjunction f).unit.app
          ((Scheme.Modules.restrictFunctor g).obj M))).app U.unop) x
  let z := M.presheaf.map (homOfLE ((f ≫ g).image_preimage_le U.unop)).op x
  let y := M.presheaf.map (homOfLE (g.image_preimage_le U.unop)).op x
  have hfg : ((Scheme.Modules.restrictAdjunction (f ≫ g)).unit.app M).app U.unop x = z :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.restrictAdjunction_unit_app_app (f ≫ g) M U.unop) x
  have hg : ((Scheme.Modules.restrictAdjunction g).unit.app M).app U.unop x = y :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.restrictAdjunction_unit_app_app g M U.unop) x
  have hc := ConcreteCategory.congr_hom
    (Scheme.Modules.restrictFunctorComp_hom_app_app
      (U := (f ≫ g) ⁻¹ᵁ U.unop) f g M) z
  have hf := ConcreteCategory.congr_hom
    (Scheme.Modules.restrictAdjunction_unit_app_app f
      ((Scheme.Modules.restrictFunctor g).obj M) (g ⁻¹ᵁ U.unop)) y
  rw [hfg]
  change _ = ((Scheme.Modules.restrictAdjunction f).unit.app
    ((Scheme.Modules.restrictFunctor g).obj M)).app (g ⁻¹ᵁ U.unop)
      (((Scheme.Modules.restrictAdjunction g).unit.app M).app U.unop x)
  rw [hg, hc, hf]
  change M.presheaf.map _ (M.presheaf.map _ x) =
    M.presheaf.map _ (M.presheaf.map _ x)
  rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply]
  congr 1

end OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionCompositionAdjunction
