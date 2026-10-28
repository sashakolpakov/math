import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceExistence
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices

/-! # Compact Choices -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices

noncomputable section

/-! The original compact supported-choice functor has precisely one
geometric point once its actual block coordinates are constructed. Its
subgroup membership is literally that of the whole block or its identity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceExistence

variable {S : Scheme} {A : Over S} [GrpObj A] [IsCommMonObj A]
  (q m : ℕ) [NeZero q] (flag : Bool)
  (K : Type) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S)
  (p : A ⟶ A) [IsMonHom p]
  [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom] [Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p).hom]

local instance compactModuleAtLevel :
    Module (ZMod (q ^ m)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q m (fun _ => if flag then m else 0)
    (fun _ => by cases flag <;> simp)

variable (e : Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p) ≃+ (Fin 3 → ZMod (q ^ m)))

def geometricCompactChoice :
    AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) p (Over.mk b) :=
  (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ m)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) K b p
    (AddEquiv.refl _)).symm (CompactChoiceExistence.compactTypedChoice q m _ e flag)

theorem geometricCompactChoice_unique
    (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) p (Over.mk b)) :
    F = geometricCompactChoice q m flag K b p e := by
  apply (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ m)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) K b p
    (AddEquiv.refl _)).injective
  rw [geometricCompactChoice, Equiv.apply_symm_apply]
  exact CompactChoiceExistence.compactTypedChoice_unique q m _ e flag _

include e in
theorem geometricCompactChoice_membership
    (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ m)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) p (Over.mk b))
    (x : Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ m) p)) :
    x.toMul ≫ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ m) p ∈ F.val.subgroup.points (Over.mk b) (𝟙 _) ↔
      if flag then True else x = 0 := by
  refine (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv_membership (q ^ m)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) K b p
    (AddEquiv.refl _) F x).symm.trans ?_
  rw [CompactChoiceExistence.compactTypedChoice_unique q m _ e flag
    (AbelianScheme.IsogenyQuotient.Geometric.TateChoices.Construction.geometricSupportedAdditiveChoiceEquiv (q ^ m)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if flag then m else 0)) K b p
      (AddEquiv.refl _) F),
    CompactChoiceExistence.compactTypedChoice_subgroup]
  cases flag <;> simp

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Geometric.CompactChoices
