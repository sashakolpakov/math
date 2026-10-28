import OAI.AlgebraicGeometry.Picard.PoincareBundle.StructureUnitGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback

/-! # Section Descent Compatibility -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionDescentCompatibility

noncomputable section

/-!
# Invariance of a normalized actual section gives its geometric descent equation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ContractionPullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p q : Z ⟶ X) (h : p ≫ f = q ≫ f)
  {M : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
  (σ : (Scheme.Modules.pullback p).obj M ⟶ (Scheme.Modules.pullback q).obj M)
  (hs : Bilinear.ContractionPullback.pulledSection p s ≫ σ = Bilinear.ContractionPullback.pulledSection q s)

include hs in
/-- Removing the normalized structure-sheaf comparison gives the actual raw section gluing equation. -/
theorem raw_section : (Scheme.Modules.pullback p).map s ≫ σ =
    (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫ Bilinear.ContractionPullback.pulledSection q s := by
  have ht := congrArg (fun a => (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫ a) hs
  change (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom ≫
    ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).inv ≫ (Scheme.Modules.pullback p).map s) ≫ σ = _ at ht
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at ht
  exact ht

include hs in
/-- A section fixed by the genuine normalized gluing defines the full compatible cover morphism from the quotient structure sheaf. -/
theorem compatible :
    (Scheme.Modules.pullback p).map ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ s) ≫ σ =
    (Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pullback q).map ((AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫ s) := by
  rw [(Scheme.Modules.pullback p).map_comp, (Scheme.Modules.pullback q).map_comp]
  simp only [Category.assoc]
  rw [raw_section p q s σ hs]
  have hu := StructureUnitGluing.unit_gluing f p q h
  calc
    _ = ((Scheme.Modules.pullback p).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso p).hom) ≫ Bilinear.ContractionPullback.pulledSection q s := (Category.assoc _ _ _).symm
    _ = ((Cech.MateNormalization.standardGluing f p q h).hom.app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) ≫
        (Scheme.Modules.pullback q).map (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso f).hom ≫
        (AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso q).hom) ≫ Bilinear.ContractionPullback.pulledSection q s := congrArg (fun a => a ≫ Bilinear.ContractionPullback.pulledSection q s) hu
    _ = _ := by simp only [Bilinear.ContractionPullback.pulledSection, Category.assoc, Iso.hom_inv_id_assoc]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.SectionDescentCompatibility
