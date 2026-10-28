import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.KernelCharacterSquares
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality

/-! # Parameter Character Squares -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterCharacterSquares

noncomputable section

/-! Parameterized Cartier sections retain their actual character values
under a commuting square of covers, after every base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality.Construction.KernelCharacters

universe u
variable {S : Scheme.{u}} {A B A' B' : Over S}
  [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
  (s : B' ⟶ B) (t : A' ⟶ A) [IsMonHom s] [IsMonHom t]
  (w : t ≫ f = f' ≫ s)

def kernelSquareGroupMap : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f') ⟶ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f) :=
  Grp.homMk (KernelCharacterSquares.kernelSquareMap f f' s t w)

def squareCharacterSection (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q)) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f'))).obj.obj (.op Q) :=
  (CartierDuality.CharacterSheaf.Construction.Schemes.characterRestriction (kernelSquareGroupMap f f' s t w)).hom.app (.op Q) χ

theorem squareCharacterSection_value (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))
    (x : Q ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f') :
    CartierDuality.Evaluation.Construction.CharacterEvaluation.value (squareCharacterSection f f' s t w Q χ) x =
      CartierDuality.Evaluation.Construction.CharacterEvaluation.value χ (x ≫ KernelCharacterSquares.kernelSquareMap f f' s t w) := rfl

include w in
omit [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
  [IsMonHom f] [IsMonHom f'] [IsMonHom s] [IsMonHom t] in
theorem square_pullback (Q : Over S) :
    (Over.pullback Q.hom).map t ≫ (Over.pullback Q.hom).map f =
      (Over.pullback Q.hom).map f' ≫ (Over.pullback Q.hom).map s := by
  rw [← Functor.map_comp, w, Functor.map_comp]

omit [IsMonHom t] in
theorem kernelSquareMap_baseChangePoint (Q : Over S) (U : Over Q.left)
    (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f')) :
    CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U
      (x ≫ KernelCharacterSquares.kernelSquareMap ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
        ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t) (square_pullback f f' s t w Q)) =
      CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f' U x ≫ KernelCharacterSquares.kernelSquareMap f f' s t w := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion, Category.assoc, KernelCharacterSquares.kernelSquareMap_inclusion,
    ← Category.assoc, CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_comp, Category.assoc, KernelCharacterSquares.kernelSquareMap_inclusion,
    ← Category.assoc, CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion]

theorem parameterKernelCharacter_square (Q : Over S)
    (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))
    (U : Over Q.left) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map f')) :
    CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f' Q (squareCharacterSection f f' s t w Q χ) U x =
      KernelCharacterSquares.squareKernelCharacter ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
        ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t) (square_pullback f f' s t w Q)
        (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterKernelCharacter f Q χ) U x := by
  change CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)
      (χ.app (.op (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))
        (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f' U x ≫ KernelCharacterSquares.kernelSquareMap f f' s t w)) =
    CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom ((Over.map Q.hom).obj U)
      (χ.app (.op (Over.mk (CartierDuality.CharacterUnitValues.Construction.KernelCharacters.parameterProjection Q U)))
        (CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint Q.hom f U
          (x ≫ KernelCharacterSquares.kernelSquareMap ((Over.pullback Q.hom).map f) ((Over.pullback Q.hom).map f')
            ((Over.pullback Q.hom).map s) ((Over.pullback Q.hom).map t)
              (square_pullback f f' s t w Q))))
  rw [kernelSquareMap_baseChangePoint f f' s t w Q U x]

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.ParameterCharacterSquares
