import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterizedLineCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterSection

/-! # Parameter Picard Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterPicardSurjectivity

noncomputable section

/-! Every pullback-trivial line over an affine parameter family is the
line of an actual Cartier character section of the original kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]
variable (Q : Over (Spec (.of k))) [IsAffine Q.left]

theorem parameterLine_kernel_character_exists
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
    (eL : (Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left) :
    ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      Nonempty (L.sheaf ≅ (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf) := by
  obtain ⟨χ, hχ, hL⟩ := ParameterizedLineCharacters.Construction.parameterPullbackTrivialLine_from_kernelCharacter f Q L eL
  let ψ := ParameterSection.Construction.parameterSectionOfUnitCharacter Q f χ hχ
  have heq : CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ = χ := by
    funext T
    apply MonoidHom.ext
    intro z
    exact ParameterSection.Construction.parameterSectionOfUnitCharacter_value Q f χ hχ T z
  have : IsAffineHom ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).1
  have : Flat ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.1
  have : Surjective ((Over.pullback Q.hom).map f).left := (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f).2.2
  have hline : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q ψ = ParameterizedLineCharacters.Construction.rawParameterCharacterLine f Q χ hχ :=
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.characterDescendedLine_congr ((Over.pullback Q.hom).map f)
      (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q ψ) χ (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q ψ) hχ heq
  exact ⟨ψ, (congrArg (fun M => Nonempty (L.sheaf ≅ M.sheaf)) hline).mpr hL⟩

theorem parameterLine_kernel_character_unique
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback Q.hom).obj B).left)
    (eL : (Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left) :
    ∃! χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) := by
  obtain ⟨χ, hχ⟩ := parameterLine_kernel_character_exists f Q L eL
  refine ⟨χ, Quotient.sound hχ, ?_⟩
  intro ψ hψ
  have : IsIso ((Over.pullback Q.hom).obj A).hom.appTop := CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A Q
  apply CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.parameterCharacterLine_class_injective f Q
    (ConcreteCategory.bijective_of_isIso ((Over.pullback Q.hom).obj A).hom.appTop).surjective
  exact hψ.symm.trans (Quotient.sound hχ)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterPicardSurjectivity
