import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ModulePullbackOpen
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.UniversalGlobalSections

/-! # Line Bundle Pullback Unit -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundlePullbackUnit.Construction

noncomputable section

/-! Descent of line-bundle morphisms under universally constant global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem isIso_pullbackMap_of_restrictMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (q : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor f).map q)] :
    IsIso ((Scheme.Modules.pullback f).map q) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback f
  have : IsIso (e.hom.app M ≫ (Scheme.Modules.pullback f).map q) := by
    rw [← e.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app M) _

theorem isIso_structureSheafToPushforward_of_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) : IsIso (TensorUnit.Construction.structureSheafToPushforward f) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  have := hf U
  exact inferInstanceAs (IsIso
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map (f.app U)))

theorem isIso_pullbackUnit_structureSheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (LineBundle.Construction.structureSheafModule Y)) := by
  have := isIso_structureSheafToPushforward_of_app f hf
  have : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (LineBundle.Construction.structureSheafModule Y) ≫
      (Scheme.Modules.pushforward f).map (LineBundle.Construction.pullbackStructureSheafIso f).hom) := by
    rw [TensorUnit.Construction.pullbackStructureSheafIso_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward f).map (LineBundle.Construction.pullbackStructureSheafIso f).hom)

theorem isIso_pullbackUnit_of_trivial {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) {M : Y.Modules} (e : M ≅ LineBundle.Construction.structureSheafModule Y) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let L := Scheme.Modules.pullback f
  let R := Scheme.Modules.pushforward f
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have := isIso_pullbackUnit_structureSheaf f hf
  have : IsIso (adj.unit.app M ≫ (L ⋙ R).map e.hom) := by
    rw [← adj.unit.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((L ⋙ R).map e.hom)

theorem isIso_app_morphismRestrict_of_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) (U : Y.Opens) (V : U.toScheme.Opens) :
    IsIso ((f ∣_ U).app V) := by
  rw [morphismRestrict_app]
  exact IsIso.comp_isIso' (hf (U.ι ''ᵁ V))
    (X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U V)).op).isIso_hom

theorem isIso_pullbackUnit_of_isLineBundle {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ U : Y.Opens, IsIso (f.app U)) {M : Y.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply ModuleLocalIso.Construction.isIso_of_locally_isIso_pullback
  intro y
  obtain ⟨U, hyU, ⟨e⟩⟩ := hM y
  let e' : M.restrict U.ι ≅ LineBundle.Construction.structureSheafModule U.toScheme :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e
  have := isIso_pullbackUnit_of_trivial (f ∣_ U)
    (isIso_app_morphismRestrict_of_app f hf U) e'
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (ModuleOpenBaseChange.Construction.moduleOpenBaseChangeNatIso f U).hom.app ((Scheme.Modules.pullback f).obj M)) := by
    rw [ModulePullbackOpen.Construction.modulePullbackOpen_unit]
    infer_instance
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) :=
    IsIso.of_isIso_comp_right _
      ((ModuleOpenBaseChange.Construction.moduleOpenBaseChangeNatIso f U).hom.app ((Scheme.Modules.pullback f).obj M))
  exact ⟨U, hyU, isIso_pullbackMap_of_restrictMap U.ι _⟩

theorem isIso_productPullbackUnit_of_isLineBundle
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y X : Over (Spec (.of k))) [IsProper X.hom] [IsIntegral X.left]
    {M : Y.left.Modules} (hM : LineBundle.Construction.IsLineBundle M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction
      (CartesianMonoidalCategory.fst Y X).left).unit.app M) :=
  isIso_pullbackUnit_of_isLineBundle (CartesianMonoidalCategory.fst Y X).left
    (UniversalGlobalSections.Construction.isIso_properBaseChange_app Y X) hM

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundlePullbackUnit.Construction
