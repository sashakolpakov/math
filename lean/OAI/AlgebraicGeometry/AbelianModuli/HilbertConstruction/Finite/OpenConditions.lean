import Mathlib.AlgebraicGeometry.Scheme

/-! # Open Conditions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OpenConditions

/-! Finite intersections of conditional open conditions detect their simultaneous range conditions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem range_subset_finite_conditional_opens {X Y : Scheme.{u}} {ι : Type v} [Finite ι]
    (f : X ⟶ Y) (P : ι → Prop) [DecidablePred P] (U : ι → Y.Opens) :
    Set.range f ⊆ ((⨅ i, if P i then U i else ⊤ : Y.Opens) : Set Y) ↔
      ∀ i, P i → Set.range f ⊆ (U i : Set Y) := by
  rw [TopologicalSpace.Opens.coe_iInf, Set.subset_iInter_iff]
  constructor
  · intro h i hi
    simpa only [ite_eq_left hi] using h i
  · intro h i
    by_cases hi : P i
    · simpa only [ite_eq_left hi] using h i hi
    · rw [ite_eq_right hi]
      exact Set.subset_univ _

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.OpenConditions
