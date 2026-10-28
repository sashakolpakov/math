import OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler

/-! # Euler Ideal -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerIdeal.Constructions

noncomputable section

/-! The original local Euler functional depends on the actual
equation ideal, so elementary equation changes preserve it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
  (rs ts : List (V.carrier.presheaf.stalk x)) (h : Ideal.ofList rs = Ideal.ofList ts) (d : ℕ)

include h

theorem supportEuler_ideal_eq (D : Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Euler.Constructions.supportEuler V p x rs d D = Euler.Constructions.supportEuler V p x ts d D := by
  by_cases hx : x ∈ (D.val : Set V.carrier)
  · rw [Euler.Constructions.supportEuler_of_mem V p x rs d D hx, Euler.Constructions.supportEuler_of_mem V p x ts d D hx]
    exact TorAlgebra.IsolatedEuler.euler_iso_left (V.carrier.presheaf.stalk x)
      (Ideal.quotientEquivAlgOfEq (V.carrier.presheaf.stalk x) h).toLinearEquiv.toModuleIso _ d
  · exact (Euler.Constructions.supportEuler_of_not_mem V p x rs d D hx).trans (Euler.Constructions.supportEuler_of_not_mem V p x ts d D hx).symm

theorem localCycleEuler_ideal_eq : Euler.Constructions.localCycleEuler V p x rs d = Euler.Constructions.localCycleEuler V p x ts d := by
  apply congrArg (Finsupp.linearCombination ℚ)
  funext D
  exact supportEuler_ideal_eq V p x rs ts h d D

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerIdeal.Constructions
