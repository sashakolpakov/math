import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyLine
import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentComponentIsomorphisms
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GlobalPullbackFrame
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Character Family Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyFrames

noncomputable section

/-! The actual character family line has a canonical pulled frame and zero-section normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Family

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Q : Over S) (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

/-- The original character datum has the actual pulled structure-sheaf frame. -/
def datumFrame : (CharacterFamilyLine.Family.datum f Q χ).obj PUnit.unit ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Q ⊗ A).left :=
  Line.Bundles.pullbackUnitIso (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q)

/-- The recovered character line is genuinely trivial on the original product cover. -/
def pullbackFrame :
    (Scheme.Modules.pullback (𝟙 Q ⊗ₘ f).left).obj (CharacterFamilyLine.Family.line f Q χ).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (Q ⊗ A).left :=
  DescentComponentIsomorphisms.componentIso Geometric.KernelLinearization.modulePullbacks (𝟙 Q ⊗ₘ f).left
    (CharacterFamilyLine.Family.recovery f Q χ) ≪≫ datumFrame f Q χ

/-- The actual lifted identity section normalizes the character line along the quotient zero section. -/
def zeroFrame :
    (Scheme.Modules.pullback (lift (𝟙 Q) (1 : Q ⟶ B)).left).obj (CharacterFamilyLine.Family.line f Q χ).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Q.left :=
  (GlobalPullbackFrame.atPoint (𝟙 Q ⊗ₘ f)
    (Line.Comparison.Bundle.fromShared (CharacterFamilyLine.Family.line f Q χ)) (pullbackFrame f Q χ).symm
    (lift (𝟙 Q) (1 : Q ⟶ A)) (lift (𝟙 Q) (1 : Q ⟶ B)) (by simp)).symm

end Family

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyFrames
