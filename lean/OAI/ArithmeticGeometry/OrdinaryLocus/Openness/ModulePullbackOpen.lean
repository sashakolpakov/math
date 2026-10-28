import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModuleOpenBaseChange

/-! # Module Pullback Open -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen.Construction

noncomputable section

/-! Pullback and its adjunction unit commute with open base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def moduleOpenBaseChangeSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    TwoSquare (Scheme.Modules.pushforward f)
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι) (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.pushforward (f ∣_ U)) :=
  TwoSquare.mk _ _ _ _ (ModuleOpenBaseChange.Construction.moduleOpenBaseChangeNatIso f U).hom

def pushforwardOpenSquareIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

theorem isIso_mate_moduleOpenBaseChangeSquare {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) :
    IsIso (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
      (Scheme.Modules.restrictAdjunction U.ι) (moduleOpenBaseChangeSquare f U)).natTrans := by
  let a := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let b := Scheme.Modules.restrictAdjunction U.ι
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have hη : IsIso (b.unit.app
      ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj M))) :=
    b.isIso_unit_app_of_iso ((pushforwardOpenSquareIso f U).app M)
  change IsIso ((mateEquiv a b (moduleOpenBaseChangeSquare f U)).app M)
  simp only [mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, Category.id_comp]
  change IsIso (b.unit.app
      ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
    (Scheme.Modules.pushforward U.ι).map ((ModuleOpenBaseChange.Construction.moduleOpenBaseChangeNatIso f U).hom.app
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
    (Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.pushforward (f ∣_ U)).map (a.counit.app M)) ≫ 𝟙 _)
  have : IsIso (a.counit.app M) := by dsimp [a]; infer_instance
  infer_instance

def modulePullbackOpenSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    TwoSquare (Scheme.Modules.restrictFunctor U.ι) (Scheme.Modules.pullback f)
      (Scheme.Modules.pullback (f ∣_ U)) (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι) :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))).symm (moduleOpenBaseChangeSquare f U)

theorem isIso_modulePullbackOpenSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsIso (modulePullbackOpenSquare f U).natTrans := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  have hm : mateEquiv a b (modulePullbackOpenSquare f U) = moduleOpenBaseChangeSquare f U :=
    (mateEquiv a b).apply_symm_apply _
  have h := iterated_mateEquiv_conjugateEquiv a b c d (modulePullbackOpenSquare f U)
  rw [hm] at h
  have hi := isIso_mate_moduleOpenBaseChangeSquare f U
  have : IsIso (conjugateEquiv (a.comp d) (c.comp b) (modulePullbackOpenSquare f U).natTrans) :=
    h ▸ hi
  exact conjugateEquiv_of_iso (a.comp d) (c.comp b) _

def modulePullbackOpenNatIso {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι := by
  have := isIso_modulePullbackOpenSquare f U
  exact asIso (modulePullbackOpenSquare f U).natTrans

theorem modulePullbackOpen_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (ModuleOpenBaseChange.Construction.moduleOpenBaseChangeNatIso f U).hom.app ((Scheme.Modules.pullback f).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
        (Scheme.Modules.pushforward (f ∣_ U)).map ((modulePullbackOpenNatIso f U).hom.app M) :=
  unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)) (moduleOpenBaseChangeSquare f U) M

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen.Construction
