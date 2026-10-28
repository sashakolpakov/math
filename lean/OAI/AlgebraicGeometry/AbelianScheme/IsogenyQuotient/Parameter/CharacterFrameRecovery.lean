import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CharacterLineRecovery
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterSection
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts

/-! # Character Frame Recovery -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterFrameRecovery.Construction

noncomputable section

/-! An actual pullback frame recovers a parameterized Cartier character
whenever the kernel-product projection preserves global functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
  (Q : Over S)
  [IsIso (fst (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)) ((Over.pullback Q.hom).obj A)).left.appTop]

theorem exists_parameterCharacter_of_pullback_frame
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
    (e : (Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left) :
    ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L := by
  let f' := (Over.pullback Q.hom).map f
  have : IsAffineHom f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective f'.left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  let κ (U : Over Q.left) := Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f' L e) U
  have hκ {U V : Over Q.left} (a : V ⟶ U) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
      Units.map a.left.appTop.hom (κ U z) = κ V (a ≫ z) :=
    Kernel.ScalarUnitCharacter.Construction.kernelScalarUnitCharacter_natural (Picard.Homomorphisms.LineKernelCocycle.Construction.pullbackLineKernelCocycle f' L e) a z
  let χ := CharacterSection.Construction.parameterCharacterSection f Q κ hκ
  refine ⟨χ, ?_⟩
  have he := CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr f' (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) κ
    (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ) hκ (CharacterSection.Construction.parameterCharacterSection_recovers f Q κ hκ)
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f' _ _) = _
  rw [he]
  exact (Quotient.sound (Kernel.CharacterLineRecovery.Construction.kernelCharacterLineRecovery f' L e)).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterFrameRecovery.Construction
