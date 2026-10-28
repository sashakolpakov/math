import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.KernelTorsionComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafTorsionMaps

/-! # Multiplication Kernel Sheaf Comparison -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison

noncomputable section

/-! The character-descent multiplication kernel and IsogenyQuotient's native
torsion represent the same sheaf kernel with the same inclusion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℕ)

def multiplicationKernelInclusionGroup : Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 G.X) ^ n)) ⟶ G :=
  Grp.homMk (Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n))

theorem multiplicationKernelSheafIso_inclusion :
    (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso G n).hom ≫ kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n) =
      CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (multiplicationKernelInclusionGroup G n) := by
  have hg : (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso G n).hom ≫ CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n =
      multiplicationKernelInclusionGroup G n := by
    apply Grp.hom_ext
    change (𝟙 _) ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n) = Picard.Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 G.X) ^ n)
    exact Category.id_comp _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso G n).hom ≫ a)
      (CartierDuality.SheafTorsionMaps.Construction.Schemes.nativeTorsionSheafIso_inclusion G n)).trans
        ((CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelGroupIso G n).hom (CartierDuality.TorsionSheaves.Construction.Schemes.nativeTorsionInclusion G n)).symm.trans
          (congrArg CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap hg)))

theorem multiplicationKernelNativeGroupIso_inv_inclusion :
    (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv ≫ multiplicationKernelInclusionGroup G n =
      Torsion.SheafComparison.Construction.kernelTorsionInclusion G n := by
  apply Grp.hom_ext
  have h : (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv.hom.hom ≫
      (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).hom.hom.hom = 𝟙 _ :=
    congrArg (fun a => a.hom.hom) (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv_hom_id
  exact (congrArg (fun a => (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv.hom.hom ≫ a)
    (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso_inclusion G n).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (fun a => a ≫ Torsion.Groups.Construction.nativeTorsionInclusion G.X n) h).trans
        (Category.id_comp _)))

theorem multiplicationKernelSheafIso_native :
    CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv ≫
      (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso G n).hom = (Torsion.SheafComparison.Construction.kernelTorsionSheafIso G n).hom := by
  apply (cancel_mono (kernel.ι (CartierDuality.TorsionSheaves.Construction.Schemes.sheafPower (CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb S G) n))).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv ≫ a)
      (multiplicationKernelSheafIso_inclusion G n)).trans
        ((CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_comp (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv
          (multiplicationKernelInclusionGroup G n)).symm.trans
            ((congrArg CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (multiplicationKernelNativeGroupIso_inv_inclusion G n)).trans
              (Torsion.SheafComparison.Construction.kernelTorsionSheafIso_inclusion G n).symm)))

theorem multiplicationKernelSheafIso_native_value (Q : Over S) (x : Q ⟶ Torsion.Groups.Construction.nativeTorsionScheme G.X n) :
    (CartierDuality.KernelTorsionComparison.Construction.Schemes.multiplicationKernelSheafIso G n).hom.hom.app (.op Q)
      (ULift.up (x ≫ (CharacterTorsionComparison.Construction.multiplicationKernelNativeGroupIso G n).inv.hom.hom)) =
        (Torsion.SheafComparison.Construction.kernelTorsionSheafIso G n).hom.hom.app (.op Q) (ULift.up x) :=
  congrArg (fun a => a.hom.app (.op Q) (ULift.up x)) (multiplicationKernelSheafIso_native G n)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MultiplicationKernelSheafComparison
