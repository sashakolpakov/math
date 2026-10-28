import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.InvariantMorphismExt
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.LineDescentUniqueness

/-! # Pullback Faithful -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.PullbackFaithful

noncomputable section

/-!
# Faithfully flat affine pullback detects equality of maps into line bundles
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.OrdinaryDatum.Ordinary OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MateNormalization
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.GlobalLineDescent

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (P : Bundles.LineBundle Y)

/-- The original line has its tautological recovery on the cover. -/
def canonicalRecovery : (Scheme.Modules.pullback f).obj P.sheaf ≅ (Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf).obj PUnit.unit := Iso.refl _

/-- This actual tautological recovery respects the full geometric gluing square. -/
theorem canonicalRecovery_compatible :
    (Scheme.Modules.pullback (pullback.fst f f)).map (canonicalRecovery f P).hom ≫
      (Geometric.CechInvariant.relationGluing f (Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf)).hom =
    (Cech.MateNormalization.standardGluing f (pullback.fst f f) (pullback.snd f f) pullback.condition).hom.app P.sheaf ≫
      (Scheme.Modules.pullback (pullback.snd f f)).map (canonicalRecovery f P).hom := by
  change (Scheme.Modules.pullback (pullback.fst f f)).map (𝟙 _) ≫ _ =
    _ ≫ (Scheme.Modules.pullback (pullback.snd f f)).map (𝟙 _)
  erw [(Scheme.Modules.pullback (pullback.fst f f)).map_id,
    (Scheme.Modules.pullback (pullback.snd f f)).map_id, Category.id_comp, Category.comp_id]
  exact Recovered.OrdinaryDatum.Ordinary.baseDatum_gluing f P.sheaf

variable [IsAffineHom f] [Flat f] [Surjective f] [IsLocallyNoetherian Y]

/-- Effective geometric descent identifies the original line with its actual canonical invariant. -/
def canonicalInvariantIso : P.sheaf ≅ (Ordinary.GlobalLineDescent.descendedLine f (Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf) (P.isLine.pullback f)).sheaf :=
  (Ordinary.LineDescentUniqueness.existsUnique_iso f (Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf) (P.isLine.pullback f)
    P (canonicalRecovery f P) (canonicalRecovery_compatible f P)).choose

/-- Actual faithfully flat affine pullback detects equality of arbitrary sheaf maps into a line bundle. -/
theorem hom_ext {M : Y.Modules} (a b : M ⟶ P.sheaf)
    (h : (Scheme.Modules.pullback f).map a = (Scheme.Modules.pullback f).map b) : a = b :=
  Geometric.InvariantMorphismExt.hom_ext_of_recovery f (pullback.fst f f) (pullback.snd f f)
    pullback.condition ((Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf).obj PUnit.unit) (Geometric.CechInvariant.relationGluing f (Recovered.OrdinaryDatum.Ordinary.baseDatum f P.sheaf))
    (canonicalInvariantIso f P) a b h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.PullbackFaithful
