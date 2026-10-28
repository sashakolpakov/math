import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.ZeroDifferential
import Mathlib.Tactic.FinCases

/-! # Pair Indices -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PairIndices.CechPairIndices

noncomputable section

/-!
# The two singleton indices of a Čech pair

The first coface selects the second member of a pair; the second coface
selects the first. These are equalities of the actual formal Čech nerve
indices, without a change to the chosen products or cochain complex.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Simplicial

universe u v w

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {ι : Type w} (U : ι → C)

def pair (i j : ι) : Fin 2 → ι := Fin.cases i (fun _ => j)

theorem zero (i j : ι) :
    (ZeroDifferential.CechZeroDifferential.face (FormalCoproduct.mk ι U).cech 0).f (pair i j) =
      fun _ : Fin 1 => j := by
  funext t
  fin_cases t
  rfl

theorem one (i j : ι) :
    (ZeroDifferential.CechZeroDifferential.face (FormalCoproduct.mk ι U).cech 1).f (pair i j) =
      fun _ : Fin 1 => i := by
  funext t
  fin_cases t
  rfl

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PairIndices.CechPairIndices
