import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.Tuples
import Mathlib.Algebra.BigOperators.Fin

/-! # Tuple Points -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TuplePoints.Construction

noncomputable section

/-!
An explicit point formula for the already constructed iterated kernel.
Reindexing by any finite equivalence preserves the subgroup exactly.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj BigOperators

universe u v

variable {S : Scheme.{u}} {A P : Over S} [GrpObj A] [IsCommMonObj A]

theorem tupleKernel_points_iff (s : ℕ) (F : Fin s → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (X : Over S) (t : X ⟶ P) (x : X ⟶ A) :
    x ∈ (Kernel.Tuples.Construction.tupleKernel s F).points X t ↔
      ∃ y : Fin s → (X ⟶ A), (∀ i, y i ∈ (F i).points X t) ∧ x = ∏ i, y i := by
  induction s generalizing x with
  | zero =>
      change x = 1 ↔ _
      constructor
      · intro hx
        exact ⟨Fin.elim0, (fun i => Fin.elim0 i), by simpa using hx⟩
      · rintro ⟨y, _, hxy⟩
        simpa using hxy
  | succ s ih =>
      constructor
      · rintro ⟨a, ha, b, hb, hxab⟩
        obtain ⟨y, hy, hby⟩ := (ih (fun i => F i.succ) b).mp hb
        refine ⟨Fin.cons a y, ?_, ?_⟩
        · exact Fin.cases ha hy
        · simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using
            hxab.trans (congrArg (a * ·) hby)
      · rintro ⟨y, hy, hxy⟩
        refine ⟨y 0, hy 0, ∏ i : Fin s, y i.succ, ?_, ?_⟩
        · exact (ih (fun i => F i.succ) _).mpr ⟨(fun i => y i.succ), (fun i => hy i.succ), rfl⟩
        · simpa only [Fin.prod_univ_succ] using hxy

theorem tupleKernel_points_iff_equiv {I : Type v} [Fintype I]
    (s : ℕ) (r : Fin s ≃ I) (F : I → TorsionQuotient.SubgroupFunctor.RelativeSubgroup A P)
    (X : Over S) (t : X ⟶ P) (x : X ⟶ A) :
    x ∈ (Kernel.Tuples.Construction.tupleKernel s (fun j => F (r j))).points X t ↔
      ∃ y : I → (X ⟶ A), (∀ i, y i ∈ (F i).points X t) ∧ x = ∏ i, y i := by
  rw [tupleKernel_points_iff]
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨(fun i => y (r.symm i)), ?_, ?_⟩
    · intro i
      simpa only [r.apply_symm_apply] using hy (r.symm i)
    · exact hxy.trans (r.symm.prod_comp y).symm
  · rintro ⟨y, hy, hxy⟩
    exact ⟨(fun j => y (r j)), (fun j => hy (r j)), hxy.trans (r.prod_comp y).symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TuplePoints.Construction
