import OAI.AlgebraicGeometry.CycleClass.Geometric.Extension
import OAI.AlgebraicGeometry.CycleClass.Geometric.RegularThom
import OAI.AlgebraicGeometry.CycleClass.Geometric.SingularBoundaryPurity
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Span -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Rational classes of genuine algebraic cycles

The class of an irreducible support is obtained from the normalized Thom
class of its actual smooth locus. The two proved singular-boundary
vanishings give its unique extension with support in the original closed
subvariety. Forgetting support gives the rational Betti class, and genuine
finite rational cycles act by finite linear combination.

This module is assembled only from geometric classes and proved extension
isomorphisms; its final class map has no class, comparison, or purity fields.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped BigOperators

namespace CycleClass.Geometric

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The relative class supported on the whole irreducible algebraic
subvariety, including its singular points. -/
def DimensionCycles.DimensionCycleSupport.rationalSupportedCycleClass (Z : DimensionCycles.DimensionCycleSupport V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ (2 * p) :=
  (Z.regularToSupportCohomologyIso (ModuleCat.of ℚ ℚ) (2 * p)
    Z.singularBoundaryRationalCohomology_two_mul_isZero
    Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero).hom Z.regularThomClass

/-- The supported extension restricts to the actual smooth-locus Thom class. -/
theorem DimensionCycles.DimensionCycleSupport.rationalSupportedCycleClass_restrict (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularSupportRestriction (ModuleCat.of ℚ ℚ) (2 * p)
        Z.rationalSupportedCycleClass = Z.regularThomClass :=
  ConcreteCategory.congr_hom
    (Z.regularToSupportCohomologyIso_hom_restriction (ModuleCat.of ℚ ℚ) (2 * p)
      Z.singularBoundaryRationalCohomology_two_mul_isZero
      Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero)
    Z.regularThomClass

/-- The restriction above is literally pullback along the open inclusion
of the singular-boundary complement. -/
theorem DimensionCycles.DimensionCycleSupport.rationalSupportedCycleClass_regularPullback (Z : DimensionCycles.DimensionCycleSupport V p) :
    Z.regularThomCohomologyRestriction (ModuleCat.of ℚ ℚ) (2 * p)
        Z.rationalSupportedCycleClass = Z.regularThomClass := by
  rw [← Z.relativeCohomologyTripleRestriction_regularThom (ModuleCat.of ℚ ℚ) (2 * p)]
  exact Z.rationalSupportedCycleClass_restrict

/-- This is the unique supported class with that genuine smooth restriction. -/
theorem DimensionCycles.DimensionCycleSupport.rationalSupportedCycleClass_unique (Z : DimensionCycles.DimensionCycleSupport V p)
    (c : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ (2 * p))
    (hc : Z.regularSupportRestriction (ModuleCat.of ℚ ℚ) (2 * p) c =
      Z.regularThomClass) : c = Z.rationalSupportedCycleClass :=
  Z.regularToSupportCohomologyIso_unique (ModuleCat.of ℚ ℚ) (2 * p)
    Z.singularBoundaryRationalCohomology_two_mul_isZero
    Z.singularBoundaryRationalCohomology_two_mul_add_one_isZero
    Z.regularThomClass c hc

/-- The rational absolute Betti class, with degree written as p+p to match
the actual pure-type de Rham and Hodge-class interfaces. -/
def DimensionCycles.DimensionCycleSupport.rationalCycleClass (Z : DimensionCycles.DimensionCycleSupport V p) :
    V.rationalCohomology (p + p) := by
  change AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace) (p + p)
  simpa only [two_mul] using
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyInclusion (ModuleCat.of ℚ ℚ) (TopCat.of V.analyticSpace)
      (Set.range Z.analyticInclusion)ᶜ (2 * p) Z.rationalSupportedCycleClass)

end CycleClass.Geometric

/-- The actual rational algebraic cycle-class map: finite rational linear
combination of the geometric classes of irreducible closed supports. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p →ₗ[ℚ] V.rationalCohomology (p + p) :=
  Finsupp.linearCombination ℚ (fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.rationalCycleClass)

theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p) :
    V.rationalCycleClass p z = z.sum (fun Z q => q • Z.rationalCycleClass) :=
  Finsupp.linearCombination_apply ℚ (v := fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p =>
    Z.rationalCycleClass) z

@[simp]
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCycleClass_single (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (q : ℚ) :
    V.rationalCycleClass p (Finsupp.single Z q) = q • Z.rationalCycleClass :=
  Finsupp.linearCombination_single ℚ (v := fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p =>
    Z.rationalCycleClass) q Z

theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.range_rationalCycleClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    LinearMap.range (V.rationalCycleClass p) = Submodule.span ℚ
      (Set.range (fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.rationalCycleClass)) :=
  Finsupp.range_linearCombination ℚ (v := fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p =>
    Z.rationalCycleClass)

/-- The subspace of rational algebraic cycle classes in genuine rational
singular cohomology. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalAlgebraicClasses (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule ℚ (V.rationalCohomology (p + p)) :=
  LinearMap.range (V.rationalCycleClass p)

theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_rationalAlgebraicClasses_iff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (c : V.rationalCohomology (p + p)) :
    c ∈ V.rationalAlgebraicClasses p ↔
      ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p, V.rationalCycleClass p z = c := Iff.rfl

/-- Algebraicity means a finite rational linear combination of precisely
the classes of genuine codimension-p irreducible algebraic supports. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalAlgebraicClasses_eq_span (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    V.rationalAlgebraicClasses p = Submodule.span ℚ
      (Set.range (fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.rationalCycleClass)) :=
  Finsupp.range_linearCombination ℚ (v := fun Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p =>
    Z.rationalCycleClass)

end

end OAI.AlgebraicGeometry
