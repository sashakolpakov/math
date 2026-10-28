import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.AdjointComposition

/-! # Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

noncomputable section

/-!
# Standard maps in the affine pullback composition comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

/-- Equality transport for geometric pullbacks has the corresponding direct-image mate. -/
theorem pullbackCongr_mate {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g) (Scheme.Modules.pullbackCongr h).inv =
        (Scheme.Modules.pushforwardCongr h).hom := by
  subst g
  change conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) (𝟙 _) = _
  rw [conjugateEquiv_id]
  ext M U x
  simp

variable {R S T : CommRingCat.{u}}

/-- The canonical scalar-extension comparison is the usual scalar-extension composition map. -/
theorem extensionThenTildeIso_standard (f : R ⟶ S) (g : S ⟶ T) :
    TildeComposition.extensionThenTildeIso f g =
      (Functor.associator (ModuleCat.extendScalars f.hom)
        (ModuleCat.extendScalars g.hom) (tilde.functor T)).symm ≪≫
        Functor.isoWhiskerRight (ModuleCat.extendScalarsComp f.hom g.hom).symm
          (tilde.functor T) := by
  exact AdjointComposition.postcompose
    (ModuleCat.extendRestrictScalarsAdj f.hom) (ModuleCat.extendRestrictScalarsAdj g.hom)
    (ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom) (tilde.adjunction (R := T))
    (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- Geometric pullback composition, including the contravariant composition equation for Spec. -/
def geometricCompositionIso (f : R ⟶ S) (g : S ⟶ T) :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g) ≅
      Scheme.Modules.pullback (Spec.map (f ≫ g)) :=
  Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f) ≪≫
    Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm

/-- This geometric map is the canonical mate of direct-image composition. -/
theorem geometricCompositionIso_mate (f : R ⟶ S) (g : S ⟶ T) :
    Adjunction.leftAdjointCompIso
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
      (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
        Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm) =
      geometricCompositionIso f g := by
  apply Iso.ext_inv
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))).injective
  change _ = conjugateEquiv _ _
    ((Scheme.Modules.pullbackCongr (Spec.map_comp f g).symm).inv ≫
      (Scheme.Modules.pullbackComp (Spec.map g) (Spec.map f)).inv)
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction
    (Spec.map g ≫ Spec.map f)), Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    pullbackCongr_mate, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  rfl

/-- The iterated geometric comparison uses the standard pullback composition and tilde map. -/
theorem iteratedPullbackToModuleIso_standard (f : R ⟶ S) (g : S ⟶ T) :
    TildeComposition.iteratedPullbackToModuleIso f g =
      Functor.associator (tilde.functor R) (Scheme.Modules.pullback (Spec.map f))
        (Scheme.Modules.pullback (Spec.map g)) ≪≫
        Functor.isoWhiskerLeft (tilde.functor R) (geometricCompositionIso f g) ≪≫
          TildePullback.tildePullbackIso (f ≫ g) := by
  have h := AdjointComposition.paste (tilde.adjunction (R := R))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (Scheme.Modules.pushforwardComp (Spec.map g) (Spec.map f) ≪≫
      Scheme.Modules.pushforwardCongr (Spec.map_comp f g).symm)
    (TildePullback.pushforwardSectionsIso (f ≫ g))
  rw [geometricCompositionIso_mate] at h
  have ht : Adjunction.leftAdjointCompIso (tilde.adjunction (R := R))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (f ≫ g)))
      ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
      (TildePullback.pushforwardSectionsIso (f ≫ g)) = TildePullback.tildePullbackIso (f ≫ g) := by
    rw [TildeMate.tildePullbackIso_eq_mate]
    rfl
  rw [ht] at h
  exact h

/-- The affine comparison carries the standard scalar-extension composition to geometric pullback
composition, on each actual module. -/
theorem tilde_composition_app (f : R ⟶ S) (g : S ⟶ T) (M : ModuleCat.{u} R) :
    (Scheme.Modules.pullback (Spec.map g)).map ((TildePullback.tildePullbackIso f).hom.app M) ≫
        (TildePullback.tildePullbackIso g).hom.app ((ModuleCat.extendScalars f.hom).obj M) ≫
          (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) =
      (geometricCompositionIso f g).hom.app ((tilde.functor R).obj M) ≫
        (TildePullback.tildePullbackIso (f ≫ g)).hom.app M := by
  have h := TildeComposition.tilde_composition f g
  rw [extensionThenTildeIso_standard, iteratedPullbackToModuleIso_standard] at h
  have hm := congrArg (fun e => e.hom.app M) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp] at hm
  rw [hm, ← Category.assoc]
  rw [← Functor.map_comp, Iso.hom_inv_id_app,
    (Scheme.Modules.pullback (Spec.map g)).map_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition
