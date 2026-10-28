import OAI.NumberTheory.Quaternion.Arithmetic.DifferentialHullConnected
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullNormal
import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferentialHull

/-! # Almost Simple Hull -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleHull

noncomputable section

/-! In an almost-simple algebraic group, a nonzero conjugation-stable
family of Lie directions has the whole group as its algebraic hull. -/

open scoped Classical
open Set

variable {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

local instance almostSimpleHullRationalTopology : TopologicalSpace G.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology G

theorem differentialHull_eq_top_of_almostSimple
    (hsimple : ∀ N : Subgroup G.RationalPoints, N.Normal → IsClosed (N : Set G.RationalPoints) →
      IsConnected (N : Set G.RationalPoints) → N = ⊥ ∨ N = ⊤)
    (S : Set (Matrix (Fin n) (Fin n) k)) (hS : S ⊆ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hconj : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : ArithmeticGroups.Lattices.Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S)
    (hne : ∃ A ∈ S, A ≠ 0) : ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S = ⊤ := by
  rcases hsimple (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S) (ArithmeticGroups.Lattices.DifferentialHullNormal.Construction.differentialHull_normal G S hconj)
    (DifferentialHullConnected.differentialHull_closed G S) (DifferentialHullConnected.differentialHull_connected G S hS) with hbot | htop
  · let : Finite (ArithmeticGroups.Lattices.DifferentialHullGroup.Construction.differentialHullSubgroup G S) := by rw [hbot]; infer_instance
    obtain ⟨A, hA, hA0⟩ := hne
    exact False.elim (hA0 (ArithmeticGroups.Lattices.Finite.DifferentialHull.Construction.finite_differentialHull_direction_zero G S hS hA))
  · exact htop

end

end OAI.NumberTheory.Quaternion.Arithmetic.AlmostSimpleHull
