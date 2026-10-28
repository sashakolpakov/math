import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Recovered.IntrinsicScalars
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.FramedBaseChange

/-! # Character Family Scalars -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyScalars

noncomputable section

/-! Actual character-family gluing scalars in the original product coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Family

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization

/-- The identity frame pulls back to the actual canonical unit frame. -/
theorem pulled_identity_frame {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y)) f = Line.Bundles.pullbackUnitIso f := by
  apply Iso.ext
  simp only [Homomorphisms.FramedDescentScalars.Construction.pulledModuleFrame, Iso.trans_hom, Functor.mapIso_hom, Iso.refl_hom]
  erw [(Scheme.Modules.pullback f).map_id, Category.id_comp]
  rfl

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Q : Over S) (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

omit [LocallyOfFinitePresentation f.left] in
/-- The recovered character family's scalar is its original character on the actual difference point. -/
theorem scalar_eq {T : Scheme.{u}} (q : T ⟶ (Q ⊗ B).left) (x y : T ⟶ (Q ⊗ A).left)
    (hx : x ≫ (𝟙 Q ⊗ₘ f).left = q) (hy : y ≫ (𝟙 Q ⊗ₘ f).left = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 Q ⊗ₘ f).left (CharacterFamilyLine.Family.line f Q χ).sheaf)
      (CharacterFamilyFrames.Family.pullbackFrame f Q χ) q x y hx hy =
    AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.differenceScalar ((Over.pullback Q.hom).map f) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
      (q ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (x ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (y ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q)
      (by rw [Category.assoc, CharacterFamilySquare.Family.square, ← Category.assoc, hx])
      (by rw [Category.assoc, CharacterFamilySquare.Family.square, ← Category.assoc, hy]) := by
  rw [show CharacterFamilyFrames.Family.pullbackFrame f Q χ =
    Recovered.IntrinsicScalars.Intrinsic.frame (𝟙 Q ⊗ₘ f).left (CharacterFamilyLine.Family.line f Q χ).sheaf
      (CharacterFamilyLine.Family.datum f Q χ) (CharacterFamilyLine.Family.recovery f Q χ)
      (CharacterFamilyFrames.Family.datumFrame f Q χ) from rfl]
  rw [Recovered.IntrinsicScalars.Intrinsic.scalar_eq]
  have h := AbelianScheme.CartierDuality.FramedBaseChange.Construction.LineDescent.framedDescentScalar_square
    ((Over.pullback Q.hom).map f).left (𝟙 Q ⊗ₘ f).left
    (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (CharacterFamilySquare.Family.square f Q)
    (AbelianScheme.CartierDuality.AffineIntrinsicLineDescent.Construction.LineDescent.nativeToDescentData
      (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum ((Over.pullback Q.hom).map f) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ)
        (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)))
    (Iso.refl (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left)) q x y hx hy
  erw [pulled_identity_frame (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q)] at h
  exact h.trans (AbelianScheme.CartierDuality.KernelCharacterGluing.Construction.KernelCharacters.characterLineDatum_scalar ((Over.pullback Q.hom).map f)
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ)
    (q ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q) (x ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) (y ≫ AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap A Q) _ _)

end Family

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyScalars
