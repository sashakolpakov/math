import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.FamilyTransport

/-! # Opposite Family -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OppositeFamily.IntrinsicFamily

noncomputable section

/-! Recover the ambient opposite subgroup from its original chosen
subgroup and original Cartier identification. The block inclusion is
monomorphic, so the pullback retains precisely the chosen subgroup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.OppositeCartierComparison
  Kernel.FamilyTransport.Family

variable {K : Type u} [Field K]
variable {G H B : Grp (Over (Spec (.of K)))} {A X : Over (Spec (.of K))}
variable [GrpObj A]
variable (P : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of K) G) (Q : AbelianScheme.FrobeniusKernel.CartierModel.Construction.CartierCoordinates (.of K) H)
variable (i : H ⟶ G) (d : B ≅ P.dualGroup)
variable (gin : G.X ⟶ A) (bin : B.X ⟶ A) [IsMonHom gin] [IsMonHom bin] [Mono gin]

theorem native_opposite_family :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage bin ((OppositeCartierComparison.oppositePairing P d).relativeAnnihilator
      (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback gin (Kernel.Base.fixedKernelFamily (P := X) (i.hom.hom ≫ gin)))) =
        Kernel.Base.fixedKernelFamily (P := X) ((P.oppositeInclusion Q i d).hom.hom ≫ bin) := by
  rw [Kernel.FamilyTransport.Family.pullback_fixed_comp, OppositeCartierComparison.opposite_annihilator_family P Q i d, Kernel.FamilyTransport.Family.image_fixed]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.OppositeFamily.IntrinsicFamily
