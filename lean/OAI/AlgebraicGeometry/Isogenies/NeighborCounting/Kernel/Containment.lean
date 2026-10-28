import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Projection

/-! # Containment -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment

noncomputable section

/-! The actual active chosen family embeds into the complete kernel by
putting the identity in each other chosen or opposite factor. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Projection OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models

variable {S : Scheme.{u}} {A P W : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj W]
variable (n : ℕ) {s : ℕ} (p r : Fin s → (A ⟶ A))
variable [∀ v, IsMonHom (p v)] [∀ v, IsMonHom (r v)]
variable (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
  (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p v)) (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (r v)) (W := W))
variable (active : Fin s) (multiplicative : Fin s → Bool) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)

theorem full_kernel_contains_chosen (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ (Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
      (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F v).points T t) :
    a ∈ (Models.multiplierFullKernel n p r pairing active multiplicative F).points T t := by
  apply Projection.tupleKernel_contains s _ v T t a
  exact ⟨a, ha, 1, Subgroup.one_mem _, (mul_one a).symm⟩

theorem full_kernel_contains_opposite (v : Fin s) (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.oppositeKernel n (p v) (r v) (pairing v)
      (Base.chosenKernel (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock n (p w))
        (fun w => AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion n (p w)) active multiplicative F v)).points T t) :
    a ∈ (Models.multiplierFullKernel n p r pairing active multiplicative F).points T t := by
  apply Projection.tupleKernel_contains s _ v T t a
  exact ⟨1, Subgroup.one_mem _, a, ha, (one_mul a).symm⟩

theorem full_kernel_contains_active (T : Over S) (t : T ⟶ P) (a : T ⟶ A)
    (ha : a ∈ F.points T t) :
    a ∈ (Models.multiplierFullKernel n p r pairing active multiplicative F).points T t := by
  apply Projection.tupleKernel_contains s _ active T t a
  refine ⟨a, ?_, 1, ?_, (mul_one a).symm⟩
  · simpa only [Base.chosenKernel, ↓reduceIte] using ha
  · exact Subgroup.one_mem _

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Containment
