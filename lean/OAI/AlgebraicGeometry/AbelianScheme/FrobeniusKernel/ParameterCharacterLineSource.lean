import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineSourceSquare
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines

/-! # Parameter Character Line Source -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterLineSource.Construction

noncomputable section

/-! Source homomorphisms pull back the original parametrized character
line to the line obtained by restricting its actual kernel character. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters

section Equality

variable {S : Scheme} {A B : Over S} [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

theorem characterDescendedLine_congr
    (χ ψ : ∀ T : Over S, (T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) →* Γ(T.left, ⊤)ˣ)
    (hχ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (χ T x) = χ U (t ≫ x))
    (hψ : ∀ {T U : Over S} (t : U ⟶ T) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f),
      Units.map t.left.appTop.hom (ψ T x) = ψ U (t ≫ x)) (h : χ = ψ) :
    CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f χ hχ = CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f ψ hψ := by
  cases h
  rfl

end Equality

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
variable [IsAffineHom f'.left] [Flat f'.left] [Surjective f'.left] [LocallyOfFinitePresentation f'.left]
variable (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

omit [LocallyOfFinitePresentation f.left] [LocallyOfFinitePresentation f'.left] in
theorem parameterCharacterLine_sourceSquare :
    Nonempty ((Scheme.Modules.pullback ((Over.pullback Q.hom).map b).left).obj
        (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ).sheaf ≅
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ)).sheaf) := by
  have hf := CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f
  have hg := CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom f'
  let := hf.1
  let := hf.2.1
  let := hf.2.2
  let := hg.1
  let := hg.2.1
  let := hg.2.2
  let ψ := CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ
  have hψ : ∀ {T U : Over Q.left} (t : U ⟶ T)
      (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f)),
      Units.map t.left.appTop.hom (ψ T z) = ψ U (t ≫ z) :=
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f Q χ
  let r := CharacterSourceMap.Construction.kernelCharacterSourceRestriction ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
    ((Over.pullback Q.hom).map a) ((Over.pullback Q.hom).map b) (SourceSquareBaseChange.Construction.sourceSquare_pullback Q.hom f f' a b h) ψ
  have hr : ∀ {T U : Over Q.left} (t : U ⟶ T)
      (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f')),
      Units.map t.left.appTop.hom (r T z) = r U (t ≫ z) :=
    CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
      ((Over.pullback Q.hom).map a) ((Over.pullback Q.hom).map b) (SourceSquareBaseChange.Construction.sourceSquare_pullback Q.hom f f' a b h) ψ hψ
  have he : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ) =
      CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine ((Over.pullback Q.hom).map f') r hr :=
    characterDescendedLine_congr ((Over.pullback Q.hom).map f') _ r
      (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f' Q (ParameterCharacterSourceRestriction.Construction.parameterSourceRestrictedCharacter f f' a b h Q χ)) hr
      (ParameterCharacterSourceRestriction.Construction.parameterKernelCharacter_sourceSquare_eq f f' a b h Q χ)
  obtain ⟨i⟩ := CharacterLineSourceSquare.Construction.characterDescendedLine_sourceSquare ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
    ((Over.pullback Q.hom).map a) ((Over.pullback Q.hom).map b)
    (SourceSquareBaseChange.Construction.sourceSquare_pullback Q.hom f f' a b h) ψ hψ
  exact ⟨i ≪≫ (eqToIso (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.sheaf he)).symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterLineSource.Construction
