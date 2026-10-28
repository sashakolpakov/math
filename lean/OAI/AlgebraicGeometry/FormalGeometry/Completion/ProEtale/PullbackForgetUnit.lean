import OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackUnit

/-! # Pullback Forget Unit -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetUnit.Construction

noncomputable section

/-!
# Completion: inverse image and the underlying-set comparison preserve units

The comparison is compatible with the actual adjunction unit. This keeps
the chosen integral generator fixed when identifying pulled-back torsors.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The constructed comparison preserves the unit, on the underlying presheaves. -/
theorem proEtConstructedPullbackForgetIso_unit
    (P : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    Functor.whiskerRight
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f)
        Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom
      (forget Ab.{u + 1}) ≫
        Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
          ((PullbackTypes.Construction.proEtConstructedPullbackForgetIso f).hom.app P).hom =
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f)
        (Type (u + 1)) (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).obj P)).hom := by
  rw [PullbackUnit.Construction.proEtConstructedPullback_unit, PullbackUnit.Construction.proEtConstructedPullback_unit]
  apply NatTrans.ext
  funext U
  change ((forget Ab.{u + 1}).map
      (((ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtensionUnit P.obj).app U) ≫
    (forget Ab.{u + 1}).map
      ((toSheafify (Scheme.ProEt.topology X)
        ((ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtension P.obj)).app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U))) ≫
    ((sheafifyComposeIso (Scheme.ProEt.topology X) (forget Ab.{u + 1})
      ((ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtension P.obj)).inv.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U) ≫
      (sheafifyMap (Scheme.ProEt.topology X)
        ((forget Ab.{u + 1}).leftKanExtensionCompIsoOfPreserves P.obj
          (ProetalePullback.Construction.proEtBaseChange f).op).hom).app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)) = _
  have hs := NatTrans.congr_app
    (sheafComposeIso_inv_fac (Scheme.ProEt.topology X) (forget Ab.{u + 1})
      ((ProetalePullback.Construction.proEtBaseChange f).op.leftKanExtension P.obj)) ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)
  have hn := NatTrans.congr_app
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((forget Ab.{u + 1}).leftKanExtensionCompIsoOfPreserves P.obj
        (ProetalePullback.Construction.proEtBaseChange f).op).hom) ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hs hn
  rw [Category.assoc, ← Category.assoc _ _
    ((sheafifyMap (Scheme.ProEt.topology X) _).app _)]
  erw [hs, ← hn, ← Category.assoc,
    Functor.leftKanExtensionCompIsoOfPreserves_hom_fac_app]
  rfl

/-- The actual inverse-image comparison preserves the adjunction unit. -/
theorem proEtPullbackForgetIso_unit_hom
    (P : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    Functor.whiskerRight
      (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom
      (forget Ab.{u + 1}) ≫
        Functor.whiskerLeft (ProetalePullback.Construction.proEtBaseChange f).op
          ((PullbackTypes.Construction.proEtPullbackForgetIso f).hom.app P).hom =
      (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).obj P)).hom := by
  let Q := (sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).obj P
  let a := Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) Ab.{u + 1}
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let b := Functor.sheafPullbackConstruction.sheafPullbackIso (ProetalePullback.Construction.proEtBaseChange f) (Type (u + 1))
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  apply NatTrans.ext
  funext U
  have ha := congrArg ((forget Ab.{u + 1}).map)
    (NatTrans.congr_app (PullbackUnit.Construction.proEtPullbackConstructionIso_unit_hom f Ab.{u + 1} P) U)
  have hb := NatTrans.congr_app
    (PullbackUnit.Construction.proEtPullbackConstructionIso_unit_hom f (Type (u + 1)) Q) U
  have hc := NatTrans.congr_app (proEtConstructedPullbackForgetIso_unit f P) U
  change (forget Ab.{u + 1}).map
      ((((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom.app U) ≫
    (((forget Ab.{u + 1}).map ((a.hom.app P).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)) ≫
      ((PullbackTypes.Construction.proEtConstructedPullbackForgetIso f).hom.app P).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)) ≫
      (b.inv.app Q).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)) = _
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ha hb
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  change (forget Ab.{u + 1}).map
      ((((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom.app U) ≫
    (forget Ab.{u + 1}).map ((a.hom.app P).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)) =
      (forget Ab.{u + 1}).map
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (ProetalePullback.Construction.proEtBaseChange f)
          Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P).hom.app U) at ha
  rw [← Category.assoc, ← Category.assoc]
  erw [ha]
  erw [hc, ← hb]
  rw [Category.assoc]
  have hi := NatTrans.congr_app (congrArg (fun k => k.hom) (b.hom_inv_id_app Q))
    ((ProetalePullback.Construction.proEtBaseChange f).op.obj U)
  change (b.hom.app Q).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U) ≫
    (b.inv.app Q).hom.app ((ProetalePullback.Construction.proEtBaseChange f).op.obj U) = 𝟙 _ at hi
  rw [hi]
  rfl

/-- Unit compatibility expressed directly as a morphism of sheaves of sets. -/
theorem proEtPullbackForgetIso_unit
    (P : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :
    (sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).map
      (((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous Ab.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app P) ≫
      ((ProetalePullback.Construction.proEtBaseChange f).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).map
          ((PullbackTypes.Construction.proEtPullbackForgetIso f).hom.app P) =
      ((ProetalePullback.Construction.proEtBaseChange f).sheafAdjunctionContinuous (Type (u + 1))
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget Ab.{u + 1})).obj P) := by
  apply (sheafToPresheaf (Scheme.ProEt.topology Y) (Type (u + 1))).map_injective
  exact proEtPullbackForgetIso_unit_hom f P

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ProEtale.PullbackForgetUnit.Construction
