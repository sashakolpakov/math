import OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareSections
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.RestrictionArrows
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant

/-! # Cech Coherence -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechCoherence

noncomputable section

/-!
# Coherence of the actual open base-change maps for a geometric Čech relation
-/

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.AlgebraicGeometry Opposite

universe u

/-- Direct image acts on every original presheaf arrow, including equality transports. -/
theorem pushforward_presheaf_map {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    {U V : Y.Opensᵒᵖ} (t : U ⟶ V) :
    ((Scheme.Modules.pushforward f).obj M).presheaf.map t =
      M.presheaf.map ((TopologicalSpace.Opens.map f.base).op.map t) := rfl

/-- Open restriction acts on every original presheaf arrow, including equality transports. -/
theorem restrict_presheaf_map {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (M : Y.Modules)
    {U V : X.Opensᵒᵖ} (t : U ⟶ V) :
    ((Scheme.Modules.restrictFunctor i).obj M).presheaf.map t =
      M.presheaf.map (i.opensFunctor.op.map t) := rfl

variable {X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  (f' : X' ⟶ Y') (p' q' : Z' ⟶ X') (h' : p' ≫ f' = q' ≫ f')
  (iY : Y' ⟶ Y) (iX : X' ⟶ X) (iZ : Z' ⟶ Z)
  [IsOpenImmersion iY] [IsOpenImmersion iX] [IsOpenImmersion iZ]
  (hf : iX ≫ f = f' ≫ iY) (hp : iZ ≫ p = p' ≫ iX) (hq : iZ ≫ q = q' ≫ iX)

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareBaseChange OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.SquareSections

/-- The three actual geometric open-square mates satisfy the required direct-image coherence. -/
theorem right_coherent : Cech.RestrictionArrows.RightCoherent
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.pullbackPushforwardAdjunction f')
    (Scheme.Modules.pullbackPushforwardAdjunction p) (Scheme.Modules.pullbackPushforwardAdjunction p')
    (Scheme.Modules.pullbackPushforwardAdjunction q) (Scheme.Modules.pullbackPushforwardAdjunction q')
    (SquareBaseChange.leftSquare f f' iX iY hf) (SquareBaseChange.leftSquare p p' iZ iX hp) (SquareBaseChange.leftSquare q q' iZ iX hq)
    (Geometric.CechInvariant.directImageIso f p q h) (Geometric.CechInvariant.directImageIso f' p' q' h') := by
  intro M
  simp only [SquareBaseChange.rightMate_leftSquare]
  apply Scheme.Modules.hom_ext
  intro W
  simp [Adjunction.restrict_map_app, SquareSections.baseChangeMap_app_app, Geometric.CechInvariant.directImageIso,
    pushforward_presheaf_map, restrict_presheaf_map]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  erw [← M.presheaf.map_comp, ← M.presheaf.map_comp,
    ← M.presheaf.map_comp, ← M.presheaf.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Open.CechCoherence
