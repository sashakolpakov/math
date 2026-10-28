import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterSourceMap
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.BaseChange

/-! # Source Square Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceSquareBaseChange.Construction

noncomputable section

/-! Base change preserves the original maps on scheme-theoretic kernels,
with their actual inclusions and all-test kernel-point comparisons. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] BaseChange.Construction.pulledBackGroup

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters

variable {S S' : Scheme} (s : S' ⟶ S) {A B A' B' : Over S}
variable [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
variable (f : A ⟶ B) (f' : A' ⟶ B') [IsMonHom f] [IsMonHom f']
variable (a : A' ⟶ A) (b : B' ⟶ B) [IsMonHom a] [IsMonHom b]
variable (h : a ≫ f = f' ≫ b)

include h in
omit [GrpObj A] [GrpObj B] [GrpObj A'] [GrpObj B']
    [IsMonHom f] [IsMonHom f'] [IsMonHom a] [IsMonHom b] in
theorem sourceSquare_pullback :
    (Over.pullback s).map a ≫ (Over.pullback s).map f =
      (Over.pullback s).map f' ≫ (Over.pullback s).map b :=
  ((Over.pullback s).map_comp a f).symm.trans
    ((congrArg (Over.pullback s).map h).trans ((Over.pullback s).map_comp f' b))

def kernelSourceSquareMap_baseChanged :
    Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f') ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f) :=
  CharacterSourceMap.Construction.kernelSourceSquareMap ((Over.pullback s).map f) ((Over.pullback s).map f')
    ((Over.pullback s).map a) ((Over.pullback s).map b) (sourceSquare_pullback s f f' a b h)

omit [GrpObj A] [GrpObj A'] [IsMonHom f] [IsMonHom f'] [IsMonHom a] in
theorem kernelSourceSquareMap_baseChange :
    (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f').hom ≫ kernelSourceSquareMap_baseChanged s f f' a b h =
      (Over.pullback s).map (CharacterSourceMap.Construction.kernelSourceSquareMap f f' a b h) ≫ (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f).hom := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) :=
    inferInstanceAs (Mono (equalizer.ι ((Over.pullback s).map f) 1))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f))).mp
  rw [Category.assoc, Category.assoc, Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso_inclusion]
  change (Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso s f').hom ≫
      (CharacterSourceMap.Construction.kernelSourceSquareMap ((Over.pullback s).map f) ((Over.pullback s).map f')
        ((Over.pullback s).map a) ((Over.pullback s).map b) (sourceSquare_pullback s f f' a b h) ≫
        Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) = _
  rw [CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion, ← Category.assoc, Picard.Homomorphisms.KernelBaseChange.Construction.kernelBaseChangeIso_inclusion,
    ← Functor.map_comp, ← Functor.map_comp, CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion]

omit [IsMonHom a] in
theorem kernelSourceSquareMap_baseChange_points (T : Over S')
    (z : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback s).map f')) :
    CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f T (z ≫ kernelSourceSquareMap_baseChanged s f f' a b h) =
      CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint s f' T z ≫ CharacterSourceMap.Construction.kernelSourceSquareMap f f' a b h := by
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) := inferInstanceAs (Mono (equalizer.ι f (1 : A ⟶ B)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion f)).mp
  rw [CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion]
  conv_rhs =>
    rw [Category.assoc, CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion, ← Category.assoc,
      CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.baseChangeKernelPoint_inclusion]
  change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm
      (z ≫ kernelSourceSquareMap_baseChanged s f f' a b h ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) = _
  change (CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv s (Grp.mk A) T).symm
      (z ≫ CharacterSourceMap.Construction.kernelSourceSquareMap ((Over.pullback s).map f) ((Over.pullback s).map f')
        ((Over.pullback s).map a) ((Over.pullback s).map b) (sourceSquare_pullback s f f' a b h) ≫
        Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f)) = _
  rw [CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion, ← Category.assoc]
  exact CartierDuality.KernelCharacterBaseChange.Construction.KernelCharacters.pullbackPoint_symm_comp s a T (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((Over.pullback s).map f'))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SourceSquareBaseChange.Construction
