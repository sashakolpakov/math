import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.Analysis.DifferentialForms.Manifold.DimensionVanishing
import OAI.AlgebraicGeometry.CycleClass.Geometric.Span

/-! # Projective Degree Bounds -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveDegreeBounds.IntegralProjectiveVariety

noncomputable section

/-!
# Actual dimension bounds for projective cohomology and algebraic classes

The real dimension of the derived analytic model bounds the degree of
genuine differential forms. The established de Rham comparison transfers
this vanishing to complex singular cohomology, and the actual rational
coefficient inclusion transfers it to rational singular cohomology.

Consequently a class outside the genuine rational algebraic class image
is nonzero and can occur only in codimension at most the complex dimension.
No Hodge-conjecture assumption or Poincare-duality premise is used.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Genuine de Rham cohomology vanishes above the real dimension of the
actual analytic model of the projective variety. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamCohomology_isZero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) (h : 2 * V.complexDimension < n) : IsZero (V.deRhamCohomology n) := by
  apply Analysis.DifferentialForms.Manifold.DimensionVanishing.manifoldDeRhamCohomology_isZero_of_finrank_lt
  rw [V.analyticModel_real_finrank]
  exact h

/-- The proved actual de Rham comparison gives the same upper bound for
complex singular cohomology. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexCohomology_isZero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) (h : 2 * V.complexDimension < n) : IsZero (V.complexCohomology n) :=
  (V.deRhamCohomology_isZero_of_dimension_lt n h).of_iso (V.deRhamBettiIso n).symm

/-- Injectivity of actual coefficient inclusion gives the upper bound
for rational singular cohomology. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomology_isZero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) (h : 2 * V.complexDimension < n) : IsZero (V.rationalCohomology n) := by
  let : Subsingleton (V.complexCohomology n) :=
    ModuleCat.subsingleton_of_isZero (V.complexCohomology_isZero_of_dimension_lt n h)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  apply V.rationalCohomologyInclusion_injective n
  exact Subsingleton.elim
    (show V.complexCohomology n from V.rationalCohomologyInclusion n a)
    (show V.complexCohomology n from V.rationalCohomologyInclusion n b)

/-- Every actual rational class above the dimension bound is zero. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomology_eq_zero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) (h : 2 * V.complexDimension < n) (a : V.rationalCohomology n) : a = 0 := by
  let : Subsingleton (V.rationalCohomology n) :=
    ModuleCat.subsingleton_of_isZero (V.rationalCohomology_isZero_of_dimension_lt n h)
  exact Subsingleton.elim a 0

/-- A class outside the genuine rational algebraic class image cannot be zero. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.ne_zero_of_not_mem_rationalAlgebraicClasses (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (a : V.rationalCohomology (p + p))
    (ha : a ∉ V.rationalAlgebraicClasses p) : a ≠ 0 := by
  intro h
  apply ha
  rw [h]
  exact (V.rationalAlgebraicClasses p).zero_mem

/-- Any class outside the actual rational algebraic class image lies
within the possible codimension range, even without a Hodge-type hypothesis. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.codimension_le_of_not_mem_rationalAlgebraicClasses (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (a : V.rationalCohomology (p + p))
    (ha : a ∉ V.rationalAlgebraicClasses p) : p ≤ V.complexDimension := by
  by_contra h
  have hp : V.complexDimension < p := Nat.lt_of_not_ge h
  have hn : 2 * V.complexDimension < p + p := by
    rw [two_mul]
    exact Nat.add_lt_add hp hp
  exact (V.ne_zero_of_not_mem_rationalAlgebraicClasses p a ha)
    (V.rationalCohomology_eq_zero_of_dimension_lt (p + p) hn a)

/-- An actual rational Hodge class outside the algebraic image is nonzero
and has codimension at most the complex dimension. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalHodgeClass_not_algebraic_bounds (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (a : V.rationalCohomology (p + p))
    (ha : V.IsRationalHodgeClass p a ∧ a ∉ V.rationalAlgebraicClasses p) :
    a ≠ 0 ∧ p ≤ V.complexDimension :=
  ⟨V.ne_zero_of_not_mem_rationalAlgebraicClasses p a ha.2,
    V.codimension_le_of_not_mem_rationalAlgebraicClasses p a ha.2⟩

/-- The actual finite rational cycle group above the dimension is zero,
by the absence of irreducible supports in that codimension. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalDimensionCycle_eq_zero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (h : V.complexDimension < p) (z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p) : z = 0 := by
  apply AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycle.eq_zero_of_ambient_lt z
  rw [← V.complexDimension_eq_transcendenceDimension]
  exact h

/-- The genuine rational cycle-class map in impossible codimension is zero. -/
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_eq_zero_of_dimension_lt (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p : ℕ) (h : V.complexDimension < p) : V.rationalCycleClass p = 0 := by
  apply LinearMap.ext
  intro z
  change V.rationalCycleClass p z = 0
  rw [V.rationalDimensionCycle_eq_zero_of_dimension_lt p h z, map_zero]

end

end OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveDegreeBounds.IntegralProjectiveVariety
