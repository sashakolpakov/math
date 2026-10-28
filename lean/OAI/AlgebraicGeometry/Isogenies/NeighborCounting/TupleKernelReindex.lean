import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel

/-! # Tuple Kernel Reindex -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelReindex

noncomputable section

/-! The complete chosen/opposite product is independent of its finite
index ordering. This compares IsogenyQuotient's disjoint-sum enumeration with the
paired product used by NeighborCounting on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelPoints

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

theorem reindexed_tuple_mem {I : Type*} [Fintype I] (n : ℕ) (e : Fin n ≃ I)
    (F : I → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) (T : Over S) (t : T ⟶ P) (a : T ⟶ A) :
    a ∈ (AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel n (fun v => F (e v))).points T t ↔
      ∃ b : I → (T ⟶ A), (∀ v, b v ∈ (F v).points T t) ∧ ∏ v, b v = a := by
  rw [TupleKernelPoints.tupleKernel_mem_iff]
  constructor
  · rintro ⟨b, hb, ha⟩
    refine ⟨fun v => b (e.symm v), ?_, ?_⟩
    · intro v
      simpa only [e.apply_symm_apply] using hb (e.symm v)
    · exact (Fintype.prod_equiv e b (fun v => b (e.symm v))
        (fun v => congrArg b (e.symm_apply_apply v).symm)).symm.trans ha
  · rintro ⟨b, hb, ha⟩
    exact ⟨fun v => b (e v), fun v => hb (e v),
      (Fintype.prod_equiv e (fun v => b (e v)) b (fun _ => rfl)).trans ha⟩

theorem tuple_sum_pairs (s : ℕ) (F G : Fin s → AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P) :
    AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel (Fintype.card (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s)) (fun v =>
      Sum.elim F G ((Fintype.equivFin (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s)).symm v)) =
      AbelianScheme.IsogenyQuotient.Kernel.Tuples.Construction.tupleKernel s (fun v => AbelianScheme.IsogenyQuotient.Kernel.Product.Construction.relativeKernelProduct (F v) (G v)) := by
  ext T t a
  rw [reindexed_tuple_mem _ (Fintype.equivFin (AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s)).symm,
    TupleKernelPoints.tupleKernel_mem_iff]
  constructor
  · rintro ⟨b, hb, ha⟩
    refine ⟨fun v => b (.inl v) * b (.inr v), ?_, ?_⟩
    · intro v
      exact ⟨_, hb (.inl v), _, hb (.inr v), rfl⟩
    · simpa only [Fintype.prod_sum_type, ← Finset.prod_mul_distrib] using ha
  · rintro ⟨b, hb, ha⟩
    choose x hx y hy he using hb
    refine ⟨Sum.elim x y, ?_, ?_⟩
    · intro v
      cases v with
      | inl v => exact hx v
      | inr v => exact hy v
    · rw [Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      exact (Finset.prod_congr rfl (fun v _ => (he v).symm)).trans ha

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.TupleKernelReindex
