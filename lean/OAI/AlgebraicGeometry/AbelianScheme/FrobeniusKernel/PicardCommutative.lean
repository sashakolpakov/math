import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardExactness
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels

/-! # Picard Commutative -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutative.Construction

noncomputable section

/-! The character-line map is the kernel of Picard pullback in the
abelian category of actual commutative fppf sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {k : Type u} [Field k] {g h : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k)))
variable (f : A.scheme ⟶ B.scheme) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]

def characterPicardFppfKernelFork : KernelFork (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) :=
  KernelFork.ofι (PicardCommutativeSheaf.Construction.characterToPicardFppfAb A B f) (PicardCommutativeSheaf.Construction.characterToPicardFppfAb_pullback A B f)

def characterPicardFppfKernel_isLimit : IsLimit (characterPicardFppfKernelFork A B f) := by
  have : Mono (PicardCommutativeSheaf.Construction.characterToPicardFppfAb A B f) :=
    Sheaf.mono_of_injective _ (fun T => CartierDuality.PicardMonomorphism.Construction.KernelCharacters.parameterCharacterPicardHom_injective f T.unop)
  refine CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints (PicardCommutativeSheaf.Construction.characterToPicardFppfAb A B f)
    (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) (PicardCommutativeSheaf.Construction.characterToPicardFppfAb_pullback A B f) ?_
  intro T c hc
  have hk : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A.scheme B.scheme f).hom.app (.op T) c =
      Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass A.scheme T := by
    rw [Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.trivialHomogeneousPicardClass_eq_one]
    exact (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback_apply A B f T c).symm.trans hc
  exact (PicardExactness.Construction.picardPullback_kernel_character_unique f T c hk).exists

def characterPicardFppfKernelIso :
    CartierDuality.CharacterGroupSheaf.Construction.Schemes.characterCommGroupSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)) ≅
      kernel (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) :=
  (characterPicardFppfKernel_isLimit A B f).conePointUniqueUpToIso
    (limit.isLimit (parallelPair (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) 0))

theorem characterPicardFppfKernelIso_inclusion :
    (characterPicardFppfKernelIso A B f).hom ≫ kernel.ι (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) =
      PicardCommutativeSheaf.Construction.characterToPicardFppfAb A B f :=
  IsLimit.conePointUniqueUpToIso_hom_comp (characterPicardFppfKernel_isLimit A B f)
    (limit.isLimit (parallelPair (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f) 0)) WalkingParallelPair.zero

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutative.Construction
