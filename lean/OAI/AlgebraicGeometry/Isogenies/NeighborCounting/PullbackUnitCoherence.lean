import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit

/-! # Pullback Unit Coherence -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullbackUnitCoherence

noncomputable section

/-! Coherence of the canonical structure-sheaf trivializations under
composition of arbitrary scheme pullbacks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

open OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction

theorem homEquiv_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {N : D} (q : L₁.obj M ⟶ N) :
    a₂.homEquiv M N (α.app M ≫ q) =
      a₁.homEquiv M N q ≫ (conjugateEquiv a₁ a₂ α).app N := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, R₂.map_comp,
    ← Category.assoc, ← unit_conjugateEquiv]
  rw [Category.assoc, ← (conjugateEquiv a₁ a₂ α).naturality, ← Category.assoc]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

theorem structureSheafToPushforward_comp :
    (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward g ≫
      (Scheme.Modules.pushforward g).map (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward f)) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) =
      ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext r
  rfl

theorem iteratedUnit_homEquiv :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _
        ((Scheme.Modules.pullback f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso g).hom ≫
          (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom) =
      ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward g ≫
        (Scheme.Modules.pushforward g).map (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward f) := by
  let af := Scheme.Modules.pullbackPushforwardAdjunction f
  let ag := Scheme.Modules.pullbackPushforwardAdjunction g
  have hf : af.homEquiv _ _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom = ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward f :=
    (af.homEquiv_unit _ _ _).trans (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.pullbackStructureSheafIso_unit f)
  have hg : ag.homEquiv _ _ (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso g).hom = ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.structureSheafToPushforward g :=
    (ag.homEquiv_unit _ _ _).trans (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.pullbackStructureSheafIso_unit g)
  rw [Adjunction.comp_homEquiv]
  change ag.homEquiv _ _ (af.homEquiv _ _
    ((Scheme.Modules.pullback f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso g).hom ≫
      (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom)) = _
  rw [af.homEquiv_naturality_left, hf, ag.homEquiv_naturality_right, hg]

/-- The canonical unit trivialization for a composite is the composite
of the canonical unit trivializations, with native pullback coherence. -/
theorem pullbackStructureSheafIso_comp :
    (Scheme.Modules.pullbackComp f g).hom.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) ≫
        (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso (f ≫ g)).hom =
      (Scheme.Modules.pullback f).map (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso g).hom ≫
        (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.pullbackStructureSheafIso f).hom := by
  let ac := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let ad := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let e := Scheme.Modules.pullbackComp f g
  apply (cancel_epi (e.inv.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z))).mp
  have hi : e.inv.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) ≫
      (Scheme.Modules.pullbackComp f g).hom.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z) = 𝟙 _ :=
    (e.app (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Z)).inv_hom_id
  rw [← Category.assoc, hi, Category.id_comp]
  apply (ad.homEquiv _ _).injective
  rw [homEquiv_conjugate ac ad e.inv,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    iteratedUnit_homEquiv, structureSheafToPushforward_comp]
  exact (ad.homEquiv_unit _ _ _).trans (ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit.Construction.pullbackStructureSheafIso_unit (f ≫ g))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PullbackUnitCoherence
