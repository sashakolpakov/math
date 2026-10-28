import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonCongr
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonIsos
import OAI.AlgebraicGeometry.Picard.PoincareBundle.TransitionSquares
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Scalar.ExtensionUnits

/-! # Canonical Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing

noncomputable section

/-!
# Affine presentations identify canonical module and geometric gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (i j : S ⟶ T) (h : f ≫ i = f ≫ j)

/-- Canonical scalar-extension gluing, retaining the equality of the composite coordinate maps. -/
def moduleTransition (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars i.hom).obj ((ModuleCat.extendScalars f.hom).obj M) ≅
      (ModuleCat.extendScalars j.hom).obj ((ModuleCat.extendScalars f.hom).obj M) :=
  ((ModuleCat.extendScalarsComp f.hom i.hom).app M).symm ≪≫
    eqToIso (congrArg (fun k : R ⟶ T => (ModuleCat.extendScalars k.hom).obj M) h) ≪≫
      (ModuleCat.extendScalarsComp f.hom j.hom).app M

/-- This is the scalar-coordinate transition already used for the canonical Čech cocycle. -/
theorem moduleTransition_eq_scalar (M : ModuleCat.{u} R) :
    moduleTransition f i j h M = Scalar.ExtensionUnits.transition f.hom i.hom j.hom
      (congrArg CommRingCat.Hom.hom h) M := rfl

/-- The module transition as a composition of whole isomorphisms. -/
theorem moduleTransition_eq (M : ModuleCat.{u} R) : moduleTransition f i j h M =
    ((ModuleCat.extendScalarsComp f.hom i.hom).app M).symm ≪≫
      eqToIso (congrArg (fun k : R ⟶ T => (ModuleCat.extendScalars k.hom).obj M) h) ≪≫
        (ModuleCat.extendScalarsComp f.hom j.hom).app M := rfl

/-- The three constituent maps of canonical module gluing. -/
theorem moduleTransition_hom (M : ModuleCat.{u} R) :
    (moduleTransition f i j h M).hom =
      (ModuleCat.extendScalarsComp f.hom i.hom).inv.app M ≫
        eqToHom (congrArg (fun k : R ⟶ T => (ModuleCat.extendScalars k.hom).obj M) h) ≫
          (ModuleCat.extendScalarsComp f.hom j.hom).hom.app M := rfl

/-- The geometric identification through pullback from the original base. -/
def geometricTransition :
    Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map i) ≅
      Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map j) :=
  Composition.geometricCompositionIso f i ≪≫
    Scheme.Modules.pullbackCongr (congrArg Spec.map h) ≪≫
      (Composition.geometricCompositionIso f j).symm

/-- The transition as an equality of whole natural isomorphisms. -/
theorem geometricTransition_eq : geometricTransition f i j h =
    Composition.geometricCompositionIso f i ≪≫ Scheme.Modules.pullbackCongr (congrArg Spec.map h) ≪≫
      (Composition.geometricCompositionIso f j).symm := rfl

/-- Evaluate the geometric transition as a composition of three actual comparison isomorphisms. -/
theorem geometricTransition_app (L : (Spec R).Modules) :
    (geometricTransition f i j h).app L =
      (Composition.geometricCompositionIso f i).app L ≪≫
        (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).app L ≪≫
          (Composition.geometricCompositionIso f j).symm.app L := by
  have h₁ := NatIso.trans_app (Composition.geometricCompositionIso f i)
    (Scheme.Modules.pullbackCongr (congrArg Spec.map h) ≪≫ (Composition.geometricCompositionIso f j).symm) L
  have h₂ := NatIso.trans_app (Scheme.Modules.pullbackCongr (congrArg Spec.map h))
    (Composition.geometricCompositionIso f j).symm L
  have h₀ := congrArg (fun z => z.app L) (geometricTransition_eq f i j h)
  exact h₀.trans (h₁.trans (congrArg (fun z => (Composition.geometricCompositionIso f i).app L ≪≫ z) h₂))

/-- The geometric transition has the standard component equation. -/
theorem geometricTransition_components (L : (Spec R).Modules) :
    TransitionSquares.HasTransitionComponents (Composition.geometricCompositionIso f i)
      (Scheme.Modules.pullbackCongr (congrArg Spec.map h)) (Composition.geometricCompositionIso f j)
      (geometricTransition f i j h) L :=
  TransitionSquares.hasTransitionComponents (Composition.geometricCompositionIso f i)
    (Scheme.Modules.pullbackCongr (congrArg Spec.map h)) (Composition.geometricCompositionIso f j)
    (geometricTransition f i j h) (geometricTransition_eq f i j h) L

variable (M : ModuleCat.{u} R) {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- The actual square comparing canonical module and geometric gluing. -/
def IsComparisonSquare : Prop :=
  (tilde.functor T).map (moduleTransition f i j h M).hom ≫
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) j).hom =
  (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) i).hom ≫
    (geometricTransition f i j h).hom.app L

/-- The whole affine presentation isomorphisms intertwine the canonical transitions. -/
theorem comparison_iso :
    (tilde.functor T).mapIso (moduleTransition f i j h M) ≪≫
      Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) j =
    Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) i ≪≫
      (geometricTransition f i j h).app L := by
  have ht := TransitionSquares.compose_iso_squares (tilde.functor T)
    ((ModuleCat.extendScalarsComp f.hom i.hom).app M).symm
    (eqToIso (congrArg (fun k : R ⟶ T => (ModuleCat.extendScalars k.hom).obj M) h))
    ((ModuleCat.extendScalarsComp f.hom j.hom).app M)
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) i)
    (Gluing.comparison M e (f ≫ i)) (Gluing.comparison M e (f ≫ j))
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) j)
    ((Composition.geometricCompositionIso f i).app L)
    ((Scheme.Modules.pullbackCongr (congrArg Spec.map h)).app L)
    ((Composition.geometricCompositionIso f j).app L)
    (ComparisonIsos.composition M e f i)
    (ComparisonIsos.congr M e h)
    (ComparisonIsos.composition M e f j)
  have hg := (geometricTransition_app f i j h L).trans
    (congrArg (fun z => (Composition.geometricCompositionIso f i).app L ≪≫
      (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).app L ≪≫ z)
      (TransitionSquares.natural_symm_app (Composition.geometricCompositionIso f j) L))
  exact TransitionSquares.finish_iso_square (tilde.functor T)
    (moduleTransition f i j h M) _
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) i)
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) j)
    ((geometricTransition f i j h).app L) _ (moduleTransition_eq f i j h M) hg ht

/-- This square commutes by coherence of the affine composition comparisons. -/
theorem comparison_square : IsComparisonSquare f i j h M e :=
  TransitionSquares.natural_square_of_iso_square (tilde.functor T)
    (moduleTransition f i j h M) (geometricTransition f i j h) L
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) i)
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) j)
    (comparison_iso f i j h M e)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing
