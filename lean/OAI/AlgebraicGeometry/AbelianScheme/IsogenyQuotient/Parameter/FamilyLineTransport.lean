import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily

/-! # Family Line Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.FamilyLineTransport.Construction

noncomputable section

/-! Actual product-family lines and their native parameter-base-change
forms have the same classes, and their source pullbacks commute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterFamily.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B : Over S} (f : A ⟶ B) (Q : Over S)

theorem parameterGroupMap_coordinate_square :
    ((Over.pullback Q.hom).map f).left ≫ (pullbackSymmetry Q.hom B.hom).inv =
      (pullbackSymmetry Q.hom A.hom).inv ≫ ((𝟙 Q) ⊗ₘ f).left := by
  simp only [Over.pullback_map_left, Over.tensorHom_left, Over.id_left]
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst, pullbackSymmetry_inv_comp_snd,
      pullbackSymmetry_inv_comp_snd_assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id]

def productFamilyParameterLine (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ B).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left :=
  L.pullback (pullbackSymmetry Q.hom B.hom).inv

set_option backward.isDefEq.respectTransparency false in
theorem productFamilyParameterLine_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ B).left) :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (productFamilyParameterLine Q L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  unfold CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass productFamilyParameterLine
  let e := pullbackSymmetry Q.hom B.hom
  exact (congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry B Q)).trans
    ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp e.hom e.inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)).symm.trans
      ((congrArg (fun a => AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) e.hom_inv_id).trans
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_id (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))))

theorem productFamilyParameterLine_pullback_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ B).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (productFamilyParameterLine Q L)) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullbackSymmetry Q.hom A.hom).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 Q) ⊗ₘ f).left)) := by
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (pullbackSymmetry Q.hom B.hom).inv (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L)) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, parameterGroupMap_coordinate_square,
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp]
  rfl

theorem productFamilyParameterLine_pullback_trivial (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ B).left)
    (h : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 Q) ⊗ₘ f).left) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (productFamilyParameterLine Q L)) =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
  rw [productFamilyParameterLine_pullback_class, h]
  exact AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.FamilyLineTransport.Construction
