import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackScalars

/-! # Unit Pullback Coherence -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackCoherence

noncomputable section

/-! The canonical structure-module comparisons respect composition of
scheme pullbacks. These are equalities of the actual adjunction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

theorem homEquiv_conjugate {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (α : L₂ ⟶ L₁) {M : C} {N : D} (h : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (α.app M ≫ h) =
      a₁.homEquiv M N h ≫ (conjugateEquiv a₁ a₂ α).app N := by
  rw [a₂.homEquiv_naturality_right, Adjunction.homEquiv_unit,
    ← unit_conjugateEquiv, Category.assoc,
    ← NatTrans.naturality, ← Category.assoc, ← Adjunction.homEquiv_unit]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem structureModulePullback_comp_inv :
    (Scheme.Modules.pullbackComp f g).inv.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom = (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom := by
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ac := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have hf : af.homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hg : ag.homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have hc : ac.homEquiv _ _ (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  apply (ac.homEquiv _ _).injective
  rw [homEquiv_conjugate (ag.comp af) ac,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  change ag.homEquiv _ _ (af.homEquiv _ _
      ((Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom)) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) = _
  rw [af.homEquiv_naturality_left, hf, ag.homEquiv_naturality_right, hg, hc]
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  rfl

@[reassoc]
theorem structureModulePullback_comp :
    (Scheme.Modules.pullbackComp f g).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Z) ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (f ≫ g)).hom =
    (Scheme.Modules.pullback f).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso g).hom ≫
      (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom := by
  rw [← structureModulePullback_comp_inv f g]
  simp

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.UnitPullbackCoherence
