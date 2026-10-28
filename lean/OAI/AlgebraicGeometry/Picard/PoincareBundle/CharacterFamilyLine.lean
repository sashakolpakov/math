import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilySquare
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentSquareIsomorphisms

/-! # Character Family Line -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyLine

noncomputable section

/-! CartierDuality's descended character line and its full recovery in the original parameter-product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Family

universe u

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Q : Over S) (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- The actual CartierDuality character line expressed on the original product family. -/
def line : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (Q ⊗ B).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)

/-- The supplied character's actual native datum in the original family coordinates. -/
def datum : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => (𝟙 Q ⊗ₘ f).left) :=
  (DescentSquareIsomorphisms.squareFunctor Geometric.KernelLinearization.modulePullbacks
    ((Over.pullback Q.hom).map f).left (𝟙 Q ⊗ₘ f).left (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)
    (CharacterFamilySquare.Family.square f Q)).obj
      (AbelianScheme.CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData
        (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
          (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)))

/-- The actual family line recovers the entire character datum on the original product cover. -/
def recovery :
    Pseudofunctor.DescentData.ofObj (F := Geometric.KernelLinearization.modulePullbacks)
      (f := fun (_ : PUnit.{1}) => (𝟙 Q ⊗ₘ f).left) (line f Q χ).sheaf ≅ datum f Q χ :=
  (DescentSquareIsomorphisms.canonicalIso Geometric.KernelLinearization.modulePullbacks
    ((Over.pullback Q.hom).map f).left (𝟙 Q ⊗ₘ f).left (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)
    (CharacterFamilySquare.Family.square f Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf).symm ≪≫
  (DescentSquareIsomorphisms.squareFunctor Geometric.KernelLinearization.modulePullbacks
    ((Over.pullback Q.hom).map f).left (𝟙 Q ⊗ₘ f).left (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q)
    (CharacterFamilySquare.Family.square f Q)).mapIso (AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterLineRecoveryIso f Q χ)

omit [LocallyOfFinitePresentation f.left] in
/-- This line's class is exactly the original parameter character class used to define the dual point. -/
theorem line_class : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (line f Q χ) = AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) := rfl

end Family

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyLine
