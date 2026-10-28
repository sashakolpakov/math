import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.MorphismSquares

/-! # Intrinsic Multiplication Naturality -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality

noncomputable section

/-! Multiplication-kernel representation respects maps between native groups. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes

variable {S : Scheme} (A B : Over S) [GrpObj A] [GrpObj B]
variable (f : A ⟶ B) [IsMonHom f] (n : ℕ)

def nativeAbelianGroupHom : Grp.mk A ⟶ Grp.mk B := Grp.homMk f

variable [IsCommMonObj A] [IsCommMonObj B]

theorem nativeMultiplicationKernelGroupIso_morphism :
    IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n ≫ (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk B) n).hom =
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianGroupHom A B f) n := by
  apply Grp.hom_ext
  change CharacterSourceMap.Construction.kernelSourceSquareMap ((𝟙 B) ^ n) ((𝟙 A) ^ n) f f
      (IntrinsicCartierNaturality.Construction.nativeGroupMultiplication_natural A B f n) ≫ 𝟙 _ =
    𝟙 _ ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap f n
  rw [Category.comp_id, Category.id_comp]
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 B) ^ n)) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 B) ^ n) (1 : B ⟶ B)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 B) ^ n))).mp
  exact (CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion ((𝟙 B) ^ n) ((𝟙 A) ^ n) f f
    (IntrinsicCartierNaturality.Construction.nativeGroupMultiplication_natural A B f n)).trans
      (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion f n).symm

theorem nativeMultiplicationKernelSheafIso_morphism :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n) ≫
        (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk B) n).hom =
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeAbelianGroupHom A B f)) n := by
  let a := IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelHom A B f n
  let b := CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianGroupHom A B f) n
  let eA := (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom
  let eB := (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk B) n).hom
  have he : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap eB =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap eA ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a eB).symm.trans
      ((congrArg (fun h => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap h)
        (nativeMultiplicationKernelGroupIso_morphism A B f n)).trans
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp eA b))
  exact MorphismSquares.Construction.morphismSquare_comp _ _ _ (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap eA) (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap eB)
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A) n).hom (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk B) n).hom he
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (nativeAbelianGroupHom A B f) n)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationNaturality
