import OAI.AlgebraicGeometry.CycleClass.Thom.ReferenceSectionEulerStep
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint

/-! # Euler -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions

noncomputable section

/-! The actual local Tor Euler characteristic extended linearly to
the original finite cycle group. Only supports through the point
contribute. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.StalkPrimeQuotient.Constructions.SupportScheme OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
  (rs : List (V.carrier.presheaf.stalk x)) (d : ℕ)

def supportEuler (C : Geometric.DimensionCycles.DimensionCycleSupport V p) : ℚ :=
  if hx : x ∈ (C.val : Set V.carrier) then
    TorAlgebra.Euler.Tor.euler (V.carrier.presheaf.stalk x)
      (ModuleCat.of (V.carrier.presheaf.stalk x) ((V.carrier.presheaf.stalk x) ⧸ Ideal.ofList rs))
      (ModuleCat.of (V.carrier.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hx)) d
  else 0

def localCycleEuler : Geometric.DimensionCycles.RationalDimensionCycle V p →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ (supportEuler V p x rs d)

theorem localCycleEuler_eq_sum (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    localCycleEuler V p x rs d c = ∑ C ∈ c.support, c C * supportEuler V p x rs d C := rfl

theorem supportEuler_of_not_mem (C : Geometric.DimensionCycles.DimensionCycleSupport V p) (hx : x ∉ (C.val : Set V.carrier)) :
    supportEuler V p x rs d C = 0 := dite_eq_right hx

theorem supportEuler_of_mem (C : Geometric.DimensionCycles.DimensionCycleSupport V p) (hx : x ∈ (C.val : Set V.carrier)) :
    supportEuler V p x rs d C = TorAlgebra.Euler.Tor.euler (V.carrier.presheaf.stalk x)
      (ModuleCat.of (V.carrier.presheaf.stalk x) ((V.carrier.presheaf.stalk x) ⧸ Ideal.ofList rs))
      (ModuleCat.of (V.carrier.presheaf.stalk x) (StalkPrimeQuotient.Constructions.SupportScheme.quotientRing V.carrier C.val x hx)) d := dite_eq_left hx

theorem localCycleEuler_eq_filter_sum (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    localCycleEuler V p x rs d c =
      ∑ C ∈ c.support.filter (fun C => x ∈ (C.val : Set V.carrier)), c C * supportEuler V p x rs d C := by
  rw [localCycleEuler_eq_sum]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro C hC hn
  have hx : x ∉ (C.val : Set V.carrier) := fun h => hn (Finset.mem_filter.mpr ⟨hC, h⟩)
  rw [supportEuler_of_not_mem V p x rs d C hx, mul_zero]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Local.Euler.Constructions
