/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Stratification.BasicLe

/-! # Closed Filtration -/

namespace OAI.AlgebraicGeometry.Stratification.ClosedFiltration

noncomputable section

open _root_.AlgebraicGeometry

/-!
# The canonical smooth decomposition as a closed filtration

The filtration is antitone, consecutive closed supports differ by the actual smooth piece,
and it is empty at the length of the existing finite list and thereafter.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

@[simp] theorem reducedSmoothClosedFiltration_zero (S : Closeds X) :
    Basic.reducedSmoothClosedFiltration f S 0 = S := rfl

@[simp] theorem reducedSmoothClosedFiltration_succ (S : Closeds X) (k : ℕ) :
    Basic.reducedSmoothClosedFiltration f S (k + 1) =
      Basic.reducedClosedSingularRemainder f (Basic.reducedSmoothClosedFiltration f S k) := rfl

theorem reducedSmoothClosedFiltration_succ_start (S : Closeds X) (k : ℕ) :
    Basic.reducedSmoothClosedFiltration f S (k + 1) =
      Basic.reducedSmoothClosedFiltration f (Basic.reducedClosedSingularRemainder f S) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [reducedSmoothClosedFiltration_succ, ih, reducedSmoothClosedFiltration_succ]

@[simp] theorem reducedClosedSingularRemainder_bot :
    Basic.reducedClosedSingularRemainder f ⊥ = ⊥ :=
  le_bot_iff.mp (BasicLe.reducedClosedSingularRemainder_le f ⊥)

@[simp] theorem reducedSmoothClosedFiltration_bot (k : ℕ) :
    Basic.reducedSmoothClosedFiltration f ⊥ k = ⊥ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [reducedSmoothClosedFiltration_succ, ih, reducedClosedSingularRemainder_bot]

theorem reducedSmoothClosedFiltration_succ_le (S : Closeds X) (k : ℕ) :
    Basic.reducedSmoothClosedFiltration f S (k + 1) ≤ Basic.reducedSmoothClosedFiltration f S k :=
  BasicLe.reducedClosedSingularRemainder_le f _

theorem reducedSmoothClosedFiltration_antitone (S : Closeds X) :
    Antitone (Basic.reducedSmoothClosedFiltration f S) :=
  antitone_nat_of_succ_le (reducedSmoothClosedFiltration_succ_le f S)

theorem reducedSmoothClosedFiltration_le (S : Closeds X) (k : ℕ) :
    Basic.reducedSmoothClosedFiltration f S k ≤ S :=
  reducedSmoothClosedFiltration_antitone f S (Nat.zero_le k)

/-- Each successive layer is the range of the smooth locally closed immersion. -/
theorem reducedSmoothClosedFiltration_layer (S : Closeds X) (k : ℕ) :
    Set.range (BasicLe.reducedClosedSmoothPieceι f (Basic.reducedSmoothClosedFiltration f S k)) =
      (Basic.reducedSmoothClosedFiltration f S k : Set X) \
        (Basic.reducedSmoothClosedFiltration f S (k + 1) : Set X) :=
  BasicLe.reducedClosedSmoothPiece_range f _

variable [PerfectField K] [NoetherianSpace X]

/-- The terminal index is the length of the finite list. -/
theorem reducedSmoothClosedFiltration_length (S : Closeds X) :
    Basic.reducedSmoothClosedFiltration f S (BasicLe.reducedSmoothStratification f S).length = ⊥ := by
  induction S using (wellFounded_lt (α := Closeds X)).induction with
  | h S ih =>
    by_cases hS : S = ⊥
    · subst S
      exact reducedSmoothClosedFiltration_bot f _
    · have hlen : (BasicLe.reducedSmoothStratification f S).length =
          (BasicLe.reducedSmoothStratification f (Basic.reducedClosedSingularRemainder f S)).length + 1 := by
        rw [BasicLe.reducedSmoothStratification, ite_eq_right hS, List.length_cons]
      rw [hlen, reducedSmoothClosedFiltration_succ_start]
      exact ih _ (BasicLe.reducedClosedSingularRemainder_lt f S hS)

end

end OAI.AlgebraicGeometry.Stratification.ClosedFiltration
