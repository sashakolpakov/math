import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PullbackKernelTorsion
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

/-! # Parameter Character -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ParameterCharacter.Construction

noncomputable section

/-! A line with an actual pullback frame over an affine parameter gives
an actual section of the kernel-character sheaf, with exact recovery. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

universe u
variable {k : Type u} [Field k]
  {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
  (Q : Over (Spec (.of k))) [IsAffine Q.left]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
  (s : (Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left)

def lineParameterKernelCharacter (U : Over Q.left) :
    (U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) →* Γ(U.left, ⊤)ˣ := by
  have := Parameter.PullbackKernelTorsion.Construction.parameterPullbackKernel_projection_appTop_isIso f Q
  exact ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle _ L s) U

theorem lineParameterKernelCharacter_natural {U V : Over Q.left} (a : V ⟶ U)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    Units.map a.left.appTop.hom (lineParameterKernelCharacter f Q L s U z) =
      lineParameterKernelCharacter f Q L s V (a ≫ z) := by
  have := Parameter.PullbackKernelTorsion.Construction.parameterPullbackKernel_projection_appTop_isIso f Q
  exact ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle _ L s) a z

def lineParameterCharacterSection :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q) :=
  Parameter.CharacterSection.Construction.parameterCharacterSection f Q (lineParameterKernelCharacter f Q L s)
    (lineParameterKernelCharacter_natural f Q L s)

theorem lineParameterCharacterSection_value (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (lineParameterCharacterSection f Q L s) U z =
      lineParameterKernelCharacter f Q L s U z :=
  Parameter.CharacterSection.Construction.parameterCharacterSection_value _ _ _ _ U z

variable [Surjective f.left]

theorem lineParameterCharacterSection_lineClass :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q (lineParameterCharacterSection f Q L s)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  let f' := (Over.pullback Q.hom).map f
  have : IsAffineHom f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have := Parameter.PullbackKernelTorsion.Construction.parameterPullbackKernel_projection_appTop_isIso f Q
  have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f'
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q (lineParameterCharacterSection f Q L s))
    (lineParameterKernelCharacter f Q L s)
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q (lineParameterCharacterSection f Q L s))
    (lineParameterKernelCharacter_natural f Q L s)
    (Parameter.CharacterSection.Construction.parameterCharacterSection_recovers _ _ _ _)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' _ _) = _
  rw [he]
  exact (Quotient.sound (CharacterLineRecovery.Construction.kernelCharacterLineRecovery f' L s)).symm

theorem lineParameterCharacterSection_familyClass :
    CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q (lineParameterCharacterSection f Q L s)) =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q L :=
  congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterFamilyMap B Q))
    (lineParameterCharacterSection_lineClass f Q L s)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.ParameterCharacter.Construction
