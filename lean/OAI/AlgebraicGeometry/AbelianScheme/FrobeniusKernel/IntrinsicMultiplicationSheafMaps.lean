import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicCartierNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Intertwining

/-! # Intrinsic Multiplication Sheaf Maps -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps

noncomputable section

/-! The multiplication-kernel comparison commutes with every actual
group endomorphism, including on nonreduced test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

attribute [local instance] Picard.Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

namespace Construction

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison.Construction.Schemes

variable {S : Scheme} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable (p : A ⟶ A) [IsMonHom p] (n : ℕ)

omit [IsCommMonObj A] in
def nativeAbelianEndomorphismGroup : Grp.mk A ⟶ Grp.mk A := Grp.homMk p

theorem nativeMultiplicationKernelGroupIso_natural :
    IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n ≫ (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom =
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianEndomorphismGroup A p) n := by
  apply Grp.hom_ext
  change (CharacterSourceMap.Construction.kernelSourceSquareMap ((𝟙 A) ^ n) ((𝟙 A) ^ n) p p
      (IntrinsicCartierNaturality.Construction.nativeEndomorphism_multiplication A p n)) ≫ 𝟙 _ =
    𝟙 _ ≫ CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap p n
  rw [Category.comp_id, Category.id_comp]
  have : Mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n)) :=
    inferInstanceAs (Mono (equalizer.ι ((𝟙 A) ^ n) (1 : A ⟶ A)))
  apply (cancel_mono (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A) ^ n))).mp
  exact (CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion ((𝟙 A) ^ n) ((𝟙 A) ^ n) p p
    (IntrinsicCartierNaturality.Construction.nativeEndomorphism_multiplication A p n)).trans
      (CartierDuality.CoprimeTorsionIs.Construction.CoprimeTorsion.torsionMap_inclusion p n).symm

theorem nativeMultiplicationKernelSheafIso_natural :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n) ≫
        (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom =
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso (Grp.mk A) n).hom ≫
        CartierDuality.SheafTorsionMaps.Construction.Schemes.torsionSheafMap (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (nativeAbelianEndomorphismGroup A p)) n := by
  let a := IntrinsicCartierNaturality.Construction.nativeMultiplicationKernelMap A p n
  let b := CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionGroupMap (nativeAbelianEndomorphismGroup A p) n
  let e := (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso (Grp.mk A) n).hom
  have he : CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap a ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap e =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap e ≫ CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap b :=
    (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp a e).symm.trans
      ((congrArg (fun f => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap f)
        (nativeMultiplicationKernelGroupIso_natural A p n)).trans
          (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp e b))
  exact Intertwining.Construction.intertwining_comp _ _ _ (CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap e)
    (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionSheafIso (Grp.mk A) n).hom he
    (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_natural (nativeAbelianEndomorphismGroup A p) n)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicMultiplicationSheafMaps
