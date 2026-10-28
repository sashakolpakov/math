import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceKernelComparison

/-! # Kernel Detection -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.KernelDetection.Neighbor

noncomputable section

/-! Derive the complete neighbor kernel from its unchanged active
choice. All compact factors and opposite annihilators are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Models OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CompactDetection.Neighbor OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ChoiceKernelComparison

variable {S : Scheme} {A P : Over S} [GrpObj A] [IsCommMonObj A]
  (q : ℕ) [Fact q.Prime] {s : ℕ} (c : Fin s → Bool) (i : Fin 3)
  (p r : Fin (s + 1) → (A ⟶ A)) [∀ v, IsMonHom (p v)] [∀ v, IsMonHom (r v)]
  [∀ v, IsFinite (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]
  [∀ v, Etale (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v)).hom]
  {W : Over S} [GrpObj W]
  (pairing : ∀ v, AbelianScheme.IsogenyQuotient.Annihilator.Construction.SchemeBicharacter
    (A := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v))
    (B := AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (r v)) (W := W))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

local instance neighborModule (v : Fin (s + 1)) : Module (ZMod (q ^ HeckeExponents.neighborLevel i))
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) :=
  AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.rankThreeElementaryModule_structure q (HeckeExponents.neighborLevel i) _
    (HeckeExponents.neighborExponents_bound 0 (Fin.cases false c) i v)

variable (U : ∀ v, AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.SupportedChoice A (q ^ HeckeExponents.neighborLevel i)
  (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v)) (p v) P)
  (coordinates : ∀ (v : Fin s) (K : Type) [Field K] [IsAlgClosed K]
    (b : Spec (.of K) ⟶ S) (_ : Over.mk b ⟶ P),
    Additive (Over.mk b ⟶ AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ HeckeExponents.neighborLevel i) (p v.succ)) ≃+
      (Fin 3 → ZMod (q ^ HeckeExponents.neighborLevel i)))

include coordinates in
theorem neighborFullKernel_eq :
    AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.choiceFullKernel (q ^ HeckeExponents.neighborLevel i) (s + 1)
      (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.neighborExponents 0 (Fin.cases false c) i v))
      p r pairing U =
    Kernel.Models.multiplierFullKernel (q ^ HeckeExponents.neighborLevel i) p r pairing 0 (Fin.cases false c) (U 0).val.subgroup := by
  apply ChoiceKernelComparison.choice_full_kernel_of_chosen_families
  intro v
  refine Fin.cases ?_ (fun w => ?_) v
  · simp [Kernel.Base.chosenKernel]
  · rw [Kernel.Base.chosenKernel, ite_eq_right (Fin.succ_ne_zero w)]
    exact CompactDetection.Neighbor.neighborCompactChoice_eq q c i p w (U w.succ) (coordinates w)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.KernelDetection.Neighbor
