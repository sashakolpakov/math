import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceSquareBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues

/-! # Parameter Character Source Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction

noncomputable section

/-! Parametrized Cartier characters retain the original source-square
restriction after passage to the parameter scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterUnitValues.Construction.KernelCharacters

variable {S : Scheme} {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)

def kernelSourceSquareGroupMap : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f') ⟶ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :=
  Grp.ofHom (CharacterSourceMap.Construction.kernelSourceSquareMap f f' a b h)

def parameterSourceRestrictedCharacter (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f'))).obj.obj (.op Q) :=
  (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (kernelSourceSquareGroupMap f f' a b h)).hom.app (.op Q) χ

theorem parameterKernelCharacter_sourceSquare (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))
    (U : Over Q.left) (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f')) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f' Q (parameterSourceRestrictedCharacter f f' a b h Q χ) U z =
      CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ U (z ≫ SourceSquareBaseChange.Construction.kernelSourceSquareMap_baseChanged Q.hom f f' a b h) := by
  let v (x : (Over.map Q.hom).obj U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :=
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)
      ((χ.app (.op (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))) x)
  change v (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f' U z ≫ CharacterSourceMap.Construction.kernelSourceSquareMap f f' a b h) =
    v (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U (z ≫ SourceSquareBaseChange.Construction.kernelSourceSquareMap_baseChanged Q.hom f f' a b h))
  exact congrArg v (SourceSquareBaseChange.Construction.kernelSourceSquareMap_baseChange_points Q.hom f f' a b h U z).symm

theorem parameterKernelCharacter_sourceSquare_eq (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f' Q (parameterSourceRestrictedCharacter f f' a b h Q χ) =
      CharacterSourceMap.Construction.kernelCharacterSourceRestriction ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
        ((Over.pullback Q.hom).map a) ((Over.pullback Q.hom).map b)
        (SourceSquareBaseChange.Construction.sourceSquare_pullback Q.hom f f' a b h) (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) := by
  funext U
  apply MonoidHom.ext
  intro z
  exact parameterKernelCharacter_sourceSquare f f' a b h Q χ U z

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction
