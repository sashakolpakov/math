import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelReindex
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

/-! # Choice Kernel Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceKernelComparison

noncomputable section

/-! Compare the complete kernel of the original IsogenyQuotient represented
subgroup tuple with the complete multiplier-level kernel used in the
reduction counts. Only the individual chosen families need computation;
the opposite subgroups and the product ordering are handled here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelReindex

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]
variable (n s : ℕ) (M : Fin s → Type u)
variable [∀ v, AddCommGroup (M v)] [∀ v, Module (ZMod n) (M v)] [∀ v, Finite (M v)]
variable (p r : Fin s → (A ⟶ A)) [∀ v, IsMonHom (p v)] [∀ v, IsMonHom (r v)]
variable {W : Over S} [GrpObj W]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p v)) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (r v)) (W := W))
variable (U : ∀ v, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A n (M v) (p v) P)

theorem choice_full_kernel_pairs :
    AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel n s M p r pairing U =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (U v).val.subgroup
        (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v) (U v).val.subgroup)) :=
  TupleKernelReindex.tuple_sum_pairs s (fun v => (U v).val.subgroup)
    (fun v => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v) (U v).val.subgroup)

theorem choice_full_kernel_of_chosen_families
    (active : Fin s) (multiplicative : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (hchosen : ∀ v, (U v).val.subgroup =
      Kernel.Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w)) (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w))
        active multiplicative F v) :
    AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel n s M p r pairing U = Kernel.Models.multiplierFullKernel n p r pairing active multiplicative F := by
  rw [choice_full_kernel_pairs]
  unfold Kernel.Models.multiplierFullKernel Kernel.Base.fullKernel
  congr 1
  funext v
  rw [hchosen v]
  rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceKernelComparison
