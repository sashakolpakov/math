import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.StructureCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Relative Structure Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureUnit

noncomputable section

/-!
# IntegralComparison: the relative-resolution structure isomorphism retains the original bounded ring sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

theorem unit : toSheafify (BoundedCrystalline.Site.topology f n)
    ((BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n).op ⋙ BigCrystallineCohomology.largePresheaf f) ≫
      (RelativeSheafComplex.structureIso f n).hom.hom =
    (StructureCoordinates.presheafIso f n).hom :=
  (BoundedCrystalline.Site.inclusion f n).toSheafify_pullbackSheafificationCompatibility (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
    (BoundedCrystalline.Site.topology f n) BigCrystallineSite.Object.topology (BigCrystallineCohomology.largePresheaf f)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeStructureUnit
