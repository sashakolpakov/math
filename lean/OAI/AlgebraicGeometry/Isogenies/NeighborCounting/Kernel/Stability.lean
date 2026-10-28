import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsChoiceIsotropy

/-! # Stability -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Stability

noncomputable section

/-! Derive coefficient stability for the complete integral multiplier
kernel from the original scalar action on every chosen and opposite block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (n : ℕ) {s : ℕ} (p r : Fin s → (A ⟶ A))
  [∀ v, IsMonHom (p v)] [∀ v, IsMonHom (r v)] {W : Over S} [GrpObj W]
  (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p v)) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (r v)) (W := W))
  (active : Fin s) (multiplicative : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
  (hk : F.KilledBy n) (hs : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedOn F (p active))
  (b : A ⟶ A) [IsMonHom b] (c d : Fin s → ℤ)
  (hc : ∀ v, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p v) ≫ b = (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p v)) ^ c v)
  (hd : ∀ v, AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (r v) ≫ b = (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (r v)) ^ d v)

include hk hs hc hd in
theorem multiplierFullKernel_stable :
    AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable (Models.multiplierFullKernel n p r pairing active multiplicative F) b := by
  apply AbelianScheme.IsogenyQuotient.BlockStability.Construction.tupleKernel_stable
  intro v
  let chosen := Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
    (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F v
  change AbelianScheme.IsogenyQuotient.Action.Construction.RelativeSubgroupStable
    (AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct chosen (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v) chosen)) b
  apply AbelianScheme.IsogenyQuotient.Action.Construction.relative_kernel_product_stable
  · exact AbelianScheme.IsogenyQuotient.BlockStability.Construction.relative_subgroup_stable_on_torsion_block chosen n (p v)
      (Models.multiplier_chosenKernel_killed n p active multiplicative F hk v)
      (Models.multiplier_chosenKernel_supported n p active multiplicative F hs v) b (c v) (hc v)
  · exact AbelianScheme.IsogenyQuotient.BlockStability.Construction.relative_subgroup_stable_on_torsion_block _ n (r v)
      (Models.oppositeKernel_killed n (p v) (r v) (pairing v) chosen)
      (Models.oppositeKernel_supported n (p v) (r v) (pairing v) chosen) b (d v) (hd v)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Stability
