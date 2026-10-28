import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

/-! # Parameter Family Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterFamilyMaps

noncomputable section

/-! Native parameter-family coordinates preserve an original group
map and its pullback on actual line-bundle classes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {B B' : Over S} (b : B' ⟶ B) (Q : Over S)

theorem parameterFamilyMap_groupMap :
    (Q ◁ b).left ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B' Q ≫ ((Over.pullback Q.hom).map b).left := by
  have hp : ((Over.pullback Q.hom).map b).left ≫ pullback.fst B.hom Q.hom =
      pullback.fst B'.hom Q.hom ≫ b.left := pullback.lift_fst _ _ _
  have hq : ((Over.pullback Q.hom).map b).left ≫ pullback.snd B.hom Q.hom =
      pullback.snd B'.hom Q.hom := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst, Category.assoc, hp,
      ← Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_fst, ← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  · rw [Category.assoc, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd, Category.assoc, hq,
      CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_snd, ← Over.comp_left, whiskerLeft_fst]

theorem parameterLineClass_groupMap (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left) :
    (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullbackPresheaf b).app (.op Q) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q L) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B' Q (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback ((Over.pullback Q.hom).map b).left L) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ b).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B' Q)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map b).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, parameterFamilyMap_groupMap, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterFamilyMaps
