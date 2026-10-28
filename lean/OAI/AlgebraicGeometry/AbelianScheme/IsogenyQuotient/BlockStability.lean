import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Action

/-! # Block Stability -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability.Construction

noncomputable section

/-!
Derive stability of the canonical full kernel from the scalar integral
action on each split torsion block. The conclusion includes every forced
opposite annihilator and every base-changed test scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

/-- A subgroup supported on an n-torsion block is stable under every
endomorphism whose restriction to that block is an integer scalar. -/
theorem relative_subgroup_stable_on_torsion_block
    (F : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (n : ℕ) (p : A ⟶ A) [IsMonHom p]
    (hkilled : F.KilledBy n) (hsupport : SubgroupFunctor.Construction.SupportedOn F p)
    (b : A ⟶ A) (k : ℤ)
    (hscalar : OppositeKernel.Construction.torsionBlockInclusion n p ≫ b = (OppositeKernel.Construction.torsionBlockInclusion n p) ^ k) :
    Action.Construction.RelativeSubgroupStable F b := by
  apply Action.Construction.relative_subgroup_stable_of_scalar F b k
  intro X t x hx
  let y := OppositeKernel.Construction.torsionBlockLift n p x (hkilled X t x hx) (hsupport X t x hx)
  have hy : y ≫ OppositeKernel.Construction.torsionBlockInclusion n p = x := OppositeKernel.Construction.torsionBlockLift_inclusion _ _ _ _ _
  calc
    x ≫ b = y ≫ (OppositeKernel.Construction.torsionBlockInclusion n p ≫ b) := by rw [← Category.assoc, hy]
    _ = (y ≫ OppositeKernel.Construction.torsionBlockInclusion n p) ^ k := by rw [hscalar, GrpObj.comp_zpow]
    _ = x ^ k := by rw [hy]

theorem tupleKernel_stable
    (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (b : A ⟶ A) [IsMonHom b] (hF : ∀ i, Action.Construction.RelativeSubgroupStable (F i) b) :
    Action.Construction.RelativeSubgroupStable (Kernel.Tuples.Construction.tupleKernel s F) b := by
  induction s with
  | zero =>
      intro X t x hx
      change x = 1 at hx
      change x ≫ b = 1
      rw [hx, MonObj.one_comp]
  | succ s ih =>
      exact Action.Construction.relative_kernel_product_stable (F 0) (Kernel.Tuples.Construction.tupleKernel s (fun i => F i.succ)) b
        (hF 0) (ih (fun i => F i.succ) (fun i => hF i.succ))

/-- Split scalar action implies stability of the full chosen/opposite
kernel. Stability of the quotient kernel is not a separate assumption. -/
theorem choiceFullKernel_stable
    (n s : ℕ) (M : Fin s → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod n) (M i)] [∀ i, Finite (M i)]
    (p q : Fin s → (A ⟶ A)) [∀ i, IsMonHom (p i)] [∀ i, IsMonHom (q i)]
    {W : Over S} [GrpObj W]
    (e : ∀ i, Annihilator.Construction.SchemeBicharacter (A := OppositeKernel.Construction.torsionBlock n (p i)) (B := OppositeKernel.Construction.torsionBlock n (q i)) (W := W))
    (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A n (M i) (p i) P)
    (b : A ⟶ A) [IsMonHom b]
    (scalar : ChoiceKernel.Construction.KernelIndex s → ℤ)
    (hscalar : ∀ i, OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p q i) ≫ b =
      (OppositeKernel.Construction.torsionBlockInclusion n (ChoiceKernel.Construction.choiceKernelProjector s p q i)) ^ scalar i) :
    Action.Construction.RelativeSubgroupStable (ChoiceKernel.Construction.choiceFullKernel n s M p q e U) b := by
  apply tupleKernel_stable
  intro j
  let i := (Fintype.equivFin (ChoiceKernel.Construction.KernelIndex s)).symm j
  exact relative_subgroup_stable_on_torsion_block
    (ChoiceKernel.Construction.choiceKernelFactor n s M p q e U i) n (ChoiceKernel.Construction.choiceKernelProjector s p q i)
    (ChoiceKernel.Construction.choiceKernelFactor_killed n s M p q e U i)
    (ChoiceKernel.Construction.choiceKernelFactor_supported n s M p q e U i) b (scalar i) (hscalar i)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BlockStability.Construction
