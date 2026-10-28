import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Character Picard Value -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue.Construction

noncomputable section

/-! The character-line homomorphism has exactly the relative Picard
class of the actual parameterized character line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]

theorem kernelCharacterPicardHom_relative_value (T : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (op T)) :
    (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T χ) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B T (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f T χ)) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.homogeneousPicardSheafInclusion_toSheafify B) (op T)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass f T χ)
  exact h.trans (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op T)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterHomogeneousClass_val f T χ))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterPicardValue.Construction
