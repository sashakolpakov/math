import Mathlib.Order.WellQuasiOrder
import Mathlib.Order.Minimal
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Order.Pi

/-! # Vector Kernel Finite Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VectorKernelFiniteGeneration

noncomputable section

/-! Gordan's finite-generation argument for homogeneous integral
equations: the minimal nonzero solutions form a finite antichain in a
finite product of natural numbers, and subtraction decomposes every
solution into these minimal solutions. -/
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι]

theorem natVectorSubmonoid_fg_of_sub_closed (M : AddSubmonoid (ι → ℕ))
    (hsub : ∀ x ∈ M, ∀ y ∈ M, y ≤ x → x - y ∈ M) : M.FG := by
  let P := fun x : ι → ℕ => x ∈ M ∧ x ≠ 0
  let B : Set (ι → ℕ) := {x | Minimal P x}
  have hB : B.Finite := by
    apply WellQuasiOrderedLE.finite_of_isAntichain
    intro x hx y hy hne hxy
    exact hne ((hy.eq_of_ge hx.prop hxy).symm)
  apply (AddSubmonoid.fg_iff M).mpr
  refine ⟨B, le_antisymm ?_ ?_, hB⟩
  · apply AddSubmonoid.closure_le.mpr
    intro x hx
    exact hx.prop.1
  · intro x
    induction x using (wellFounded_lt (α := ι → ℕ)).induction with
    | h x ih =>
      intro hx
      by_cases hx0 : x = 0
      · subst x
        exact (AddSubmonoid.closure B).zero_mem
      obtain ⟨y, hyx, hy⟩ := exists_minimal_le_of_wellFoundedLT P x ⟨hx, hx0⟩
      have hym : y ∈ M := hy.prop.1
      have hyn : y ≠ 0 := hy.prop.2
      have hdiff : x - y < x := by
        apply lt_iff_le_not_ge.mpr
        refine ⟨fun i => Nat.sub_le _ _, ?_⟩
        intro hge
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hyn
        have hypos : 0 < y i := Nat.pos_of_ne_zero hi
        have hxpos : 0 < x i := hypos.trans_le (hyx i)
        exact (Nat.not_le_of_lt (Nat.sub_lt hxpos hypos)) (hge i)
      have hd : x - y ∈ AddSubmonoid.closure B := ih (x - y) hdiff (hsub x hx y hym hyx)
      have hys : y ∈ AddSubmonoid.closure B := AddSubmonoid.subset_closure hy
      have hsum : x - y + y = x := by
        funext i
        exact Nat.sub_add_cancel (hyx i)
      exact hsum ▸ (AddSubmonoid.closure B).add_mem hd hys

theorem natVectorHomKernel_fg {G : Type v} [AddGroup G] (f : (ι → ℕ) →+ G) : (AddMonoidHom.mker f).FG := by
  apply natVectorSubmonoid_fg_of_sub_closed
  intro x hx y hy hyx
  have hsum : x - y + y = x := by
    funext i
    exact Nat.sub_add_cancel (hyx i)
  have h : f (x - y) + f y = f x := (f.map_add (x - y) y).symm.trans (congrArg f hsum)
  change f x = 0 at hx
  change f y = 0 at hy
  change f (x - y) = 0
  simpa only [hx, hy, add_zero] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.VectorKernelFiniteGeneration
