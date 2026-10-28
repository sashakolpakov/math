import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterLineSource

/-! # Character Line Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineBaseChange.Construction

noncomputable section

/-! The actual parameter character line commutes with arbitrary source
base change, through the native double-pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

variable {S S' : Scheme} (s : S' ⟶ S) (Q : Over S')
variable {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
variable [IsAffineHom f.left] [Flat f.left] [Surjective f.left]

local instance parameterChangedCover_affine : IsAffineHom ((Over.pullback s).map f).left :=
  (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).1

local instance parameterChangedCover_flat : Flat ((Over.pullback s).map f).left :=
  (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.1

local instance parameterChangedCover_surjective : Surjective ((Over.pullback s).map f).left :=
  (CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties s f).2.2

theorem parameterCharacterLine_baseChange
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op ((Over.map s).obj Q))) :
    Nonempty ((Scheme.Modules.pullback (ParameterBaseChange.Construction.parameterBaseChangeInv s Q B).left).obj
        (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f ((Over.map s).obj Q) χ).sheaf ≅
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ)).sheaf) := by
  let f0 := (Over.pullback ((Over.map s).obj Q).hom).map f
  let f1 := (Over.pullback Q.hom).map ((Over.pullback s).map f)
  let a := ParameterBaseChange.Construction.parameterBaseChangeInv s Q A
  let b := ParameterBaseChange.Construction.parameterBaseChangeInv s Q B
  have : IsMonHom a := ParameterBaseChange.Construction.parameterBaseChangeInv_isMonHom s Q (Grp.mk A)
  have : IsMonHom b := ParameterBaseChange.Construction.parameterBaseChangeInv_isMonHom s Q (Grp.mk B)
  have hc0 := CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties ((Over.map s).obj Q).hom f
  have hc1 := CartierDuality.CharacterLineBaseChange.Construction.KernelCharacters.baseChangedCover_properties Q.hom ((Over.pullback s).map f)
  let := hc0.1
  let := hc0.2.1
  let := hc0.2.2
  let := hc1.1
  let := hc1.2.1
  let := hc1.2.2
  let ψ := CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f ((Over.map s).obj Q) χ
  have hψ : ∀ {T U : Over Q.left} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f0),
      Units.map t.left.appTop.hom (ψ T z) = ψ U (t ≫ z) :=
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural f ((Over.map s).obj Q) χ
  let r := CharacterSourceMap.Construction.kernelCharacterSourceRestriction f0 f1 a b (ParameterBaseChange.Construction.parameterBaseChangeSquare s Q f) ψ
  have hr : ∀ {T U : Over Q.left} (t : U ⟶ T) (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f1),
      Units.map t.left.appTop.hom (r T z) = r U (t ≫ z) :=
    CharacterSourceMap.Construction.kernelCharacterSourceRestriction_natural f0 f1 a b (ParameterBaseChange.Construction.parameterBaseChangeSquare s Q f) ψ hψ
  have hchar : CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter ((Over.pullback s).map f) Q
      (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) = r := by
    funext U
    apply MonoidHom.ext
    intro z
    exact ParameterCharacterBaseChange.Construction.parameterKernelCharacter_baseChange s Q f χ U z
  have he : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine ((Over.pullback s).map f) Q
      (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ) = CartierDuality.EffectiveKernelCharacters.Construction.KernelCharacters.characterDescendedLine f1 r hr :=
    ParameterCharacterLineSource.Construction.characterDescendedLine_congr f1 _ r
      (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter_natural ((Over.pullback s).map f) Q
        (CharacterBaseChangeValues.Construction.baseChangedKernelCharacterSection s f Q χ)) hr hchar
  obtain ⟨i⟩ := CharacterLineSourceSquare.Construction.characterDescendedLine_sourceSquare f0 f1 a b (ParameterBaseChange.Construction.parameterBaseChangeSquare s Q f) ψ hψ
  exact ⟨i ≪≫ (eqToIso (congrArg AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.sheaf he)).symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterLineBaseChange.Construction
