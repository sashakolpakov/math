import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveDegreeBounds

/-! # Geometric Classes -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Rational classes of geometric algebraic cycles

The map used here is constructed from actual fundamental-class traces and
canonical Poincare duality. Its source is the finite rational coefficient
module on the genuine algebraic supports. The algebraic subspace is its
actual image, equivalently the rational span of the individual cycle classes.
-/

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

/-- Rational algebraic classes under the geometric fundamental-cycle map. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricAlgebraicClasses (p : ℕ) : Submodule ℚ (V.rationalCohomology (p + p)) :=
  LinearMap.range (V.geometricCycleClassMap p)

/-- Membership means being the image of an actual finite rational cycle. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_geometricAlgebraicClasses_iff (p : ℕ)
    (a : V.rationalCohomology (p + p)) :
    a ∈ V.geometricAlgebraicClasses p ↔
      ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p, V.geometricCycleClassMap p z = a := Iff.rfl

/-- The actual image is exactly the rational linear span of the genuine
geometric classes of the irreducible algebraic supports. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricAlgebraicClasses_eq_span (p : ℕ) :
    V.geometricAlgebraicClasses p = Submodule.span ℚ
      (Set.range (fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.geometricCycleClass)) :=
  V.range_geometricCycleClassMap p

/-- A class outside the rational algebraic image cannot be zero. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.ne_zero_of_not_mem_geometricAlgebraicClasses (p : ℕ)
    (a : V.rationalCohomology (p + p)) (ha : a ∉ V.geometricAlgebraicClasses p) :
    a ≠ 0 := by
  intro h
  apply ha
  rw [h]
  exact (V.geometricAlgebraicClasses p).zero_mem

/-- Such a class necessarily lies in the actual codimension range. This
uses the proved dimension bound for ordinary rational cohomology. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.codimension_le_of_not_mem_geometricAlgebraicClasses (p : ℕ)
    (a : V.rationalCohomology (p + p)) (ha : a ∉ V.geometricAlgebraicClasses p) :
    p ≤ V.complexDimension := by
  by_contra h
  have hp : V.complexDimension < p := Nat.lt_of_not_ge h
  have hn : 2 * V.complexDimension < p + p := by
    rw [two_mul]
    exact Nat.add_lt_add hp hp
  exact (V.ne_zero_of_not_mem_geometricAlgebraicClasses p a ha)
    (V.rationalCohomology_eq_zero_of_dimension_lt (p + p) hn a)

/-- A geometric counterexample is nonzero and has possible codimension. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClass_not_geometric_algebraic_bounds (p : ℕ)
    (a : V.rationalCohomology (p + p))
    (ha : V.IsRationalHodgeClass p a ∧ a ∉ V.geometricAlgebraicClasses p) :
    a ≠ 0 ∧ p ≤ V.complexDimension :=
  ⟨V.ne_zero_of_not_mem_geometricAlgebraicClasses p a ha.2,
    V.codimension_le_of_not_mem_geometricAlgebraicClasses p a ha.2⟩

end

end OAI.AlgebraicGeometry
