import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport

/-! # Compact Detection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor

noncomputable section

/-! Retain the original neighbor elementary module while deriving its
complete compact chosen subgroup on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceTypeTransport
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactChoiceDetection

variable {S : Scheme} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (q : ℕ) [Fact q.Prime] {s : ℕ} (c : Fin s → Bool) (i : Fin 3)
  (p : Fin (s + 1) → (A ⟶ A)) [∀ v, IsMonHom (p v)]
  (v : Fin s)
  [IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)).hom]
  [Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)).hom]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance originalModule : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v.succ)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v.succ)

local instance compactModule : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if c v then HeckeExponents.neighborLevel i else 0)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (fun _ => by split_ifs <;> omega)

variable (F : AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ HeckeExponents.neighborLevel i)
  (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v.succ)) (p v.succ) P)
  (coordinates : ∀ (K : Type) [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ S) (_ : Over.mk b ⟶ P),
    Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)) ≃+
      (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

include coordinates in
theorem neighborCompactChoice_eq :
    F.val.subgroup =
      if c v then Kernel.Base.fixedKernelFamily (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlockInclusion (q ^ HeckeExponents.neighborLevel i) (p v.succ))
      else AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.trivialRelativeSubgroup := by
  let e : AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v.succ) ≃+
      AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (fun _ => if c v then HeckeExponents.neighborLevel i else 0) := by
    rw [HeckeExponents.neighborExponents_compact 0 v.succ (Fin.succ_ne_zero v)]
    exact AddEquiv.refl _
  exact CompactChoiceDetection.compactChoice_eq q (HeckeExponents.neighborLevel i) (c v) (p v.succ)
    (ChoiceTypeTransport.supportedChoiceTypeEquiv _ _ e F) coordinates

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor
