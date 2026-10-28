import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullbackFormula

/-! # Pullback Units -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullbackUnits

noncomputable section

/-! Pullback adjunction units track sections through the actual geometric
composition comparisons. On a subordinate open, an open-immersion unit
is an isomorphism. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Construction

universe u
variable {X Y Z : Scheme.{u}}

theorem module_pullback_comp_unit (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).unit.app M ≫
      (Scheme.Modules.pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M ≫
      (Scheme.Modules.pushforward (f ≫ g)).map
        ((Scheme.Modules.pullbackComp f g).inv.app M) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  exact h

theorem open_pullback_unit_app_isIso (M : Y.Modules) (U W : Y.Opens) (hW : W ≤ U) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).app W) := by
  have hpre : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
    apply le_antisymm (U.ι.image_preimage_le W)
    intro x hx
    exact ⟨⟨x, hW hx⟩, hx, rfl⟩
  have hres : IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app W) := by
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have he : homOfLE (U.ι.image_preimage_le W) = eqToHom hpre := Subsingleton.elim _ _
    rw [he]
    have hi : IsIso (M.presheaf.map (eqToHom hpre).op) := by
      rw [eqToHom_op, eqToHom_map]
      infer_instance
    exact hi
  have h := congrArg (fun a => a.app W)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (Scheme.Modules.restrictAdjunction U.ι)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) M)
  rw [← h]
  change IsIso ((((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app W) ≫
    (((Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app M)).app W))
  infer_instance

theorem module_pullback_comp_unit_app (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U) =
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U := by
  have h := congrArg (fun a => a.app U) (module_pullback_comp_unit f g M)
  change (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U ≫
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        ((Scheme.Modules.pullback g).obj M)).app (g ⁻¹ᵁ U)) ≫ 𝟙 _ =
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app M).app U ≫
      ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) at h
  rw [Category.comp_id] at h
  rw [← Category.assoc, h]
  erw [Category.assoc]
  have he := congrArg (fun a => a.app ((f ≫ g) ⁻¹ᵁ U))
    ((Scheme.Modules.pullbackComp f g).app M).inv_hom_id
  change ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) ≫
      ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U) = 𝟙 _ at he
  erw [he, Category.comp_id]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullbackUnits
