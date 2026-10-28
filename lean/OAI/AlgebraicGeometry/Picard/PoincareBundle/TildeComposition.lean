import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

/-! # Tilde Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition

noncomputable section

/-!
# Composition compatibility of the canonical affine tilde comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PushforwardSections OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeMate

variable {R S T : CommRingCat.{u}}

/-- Composition of restriction of scalars after global sections. -/
def restrictionCompositionIso (f : R ⟶ S) (g : S ⟶ T) :
    (moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars g.hom) ⋙
        ModuleCat.restrictScalars f.hom ≅
      moduleSpecΓFunctor (R := T) ⋙ ModuleCat.restrictScalars (f ≫ g).hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSpecΓFunctor (R := T))
      (ModuleCat.restrictScalarsComp f.hom g.hom).symm

/-- The right-adjoint comparison diagram commutes. -/
theorem right_composition (f : R ⟶ S) (g : S ⟶ T) :
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward (Spec.map g))
        (TildePullback.pushforwardSectionsIso f).symm ≪≫ Affine.PushforwardSections.compositeSectionsIso f g =
      (Functor.associator (Scheme.Modules.pushforward (Spec.map g))
        (moduleSpecΓFunctor (R := S)) (ModuleCat.restrictScalars f.hom)).symm ≪≫
        Functor.isoWhiskerRight (TildePullback.pushforwardSectionsIso g) (ModuleCat.restrictScalars f.hom) ≪≫
          restrictionCompositionIso f g := by
  rw [Affine.PushforwardSections.sectionsIso_composition]
  apply Iso.ext
  simp only [Affine.PushforwardSections.iteratedSectionsIso, restrictionCompositionIso, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp, Iso.inv_hom_id,
    Functor.whiskerLeft_id', Category.id_comp]

/-- The canonical comparison from two scalar extensions followed by tilde to their composite. -/
def extensionThenTildeIso (f : R ⟶ S) (g : S ⟶ T) :
    ModuleCat.extendScalars f.hom ⋙ ModuleCat.extendScalars g.hom ⋙ tilde.functor T ≅
      ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor T :=
  Adjunction.leftAdjointCompIso (ModuleCat.extendRestrictScalarsAdj f.hom)
    ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (restrictionCompositionIso f g)

/-- The canonical comparison from two geometric pullbacks to the composite scalar extension. -/
def iteratedPullbackToModuleIso (f : R ⟶ S) (g : S ⟶ T) :
    (tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map f)) ⋙
        Scheme.Modules.pullback (Spec.map g) ≅
      ModuleCat.extendScalars (f ≫ g).hom ⋙ tilde.functor T :=
  Adjunction.leftAdjointCompIso
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (Affine.PushforwardSections.compositeSectionsIso f g)

/-- The canonical mates give a coherent comparison along the two affine pullbacks. -/
theorem tilde_composition (f : R ⟶ S) (g : S ⟶ T) :
    Functor.isoWhiskerLeft (ModuleCat.extendScalars f.hom) (TildePullback.tildePullbackIso g) ≪≫
        extensionThenTildeIso f g =
      (Functor.associator (ModuleCat.extendScalars f.hom) (tilde.functor S)
        (Scheme.Modules.pullback (Spec.map g))).symm ≪≫
        Functor.isoWhiskerRight (TildePullback.tildePullbackIso f).symm (Scheme.Modules.pullback (Spec.map g)) ≪≫
          iteratedPullbackToModuleIso f g := by
  have hg : TildePullback.tildePullbackIso g = Adjunction.leftAdjointCompIso (tilde.adjunction (R := S))
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
      ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
      (TildePullback.pushforwardSectionsIso g) := by
    rw [TildeMate.tildePullbackIso_eq_mate]
    rfl
  have h := Adjunction.leftAdjointCompIso_assoc (ModuleCat.extendRestrictScalarsAdj f.hom)
    (tilde.adjunction (R := S)) (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map g))
    ((tilde.adjunction (R := R)).comp (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj g.hom).comp (tilde.adjunction (R := T)))
    ((ModuleCat.extendRestrictScalarsAdj (f ≫ g).hom).comp (tilde.adjunction (R := T)))
    (TildePullback.pushforwardSectionsIso f).symm (TildePullback.pushforwardSectionsIso g)
    (restrictionCompositionIso f g) (Affine.PushforwardSections.compositeSectionsIso f g) (right_composition f g)
  rw [← hg, ← TildeMate.tildePullbackIso_symm_eq_compIso] at h
  exact h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TildeComposition
