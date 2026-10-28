import OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleTrace
import OAI.AlgebraicTopology.DeRham.Comparison.RegularAmbientCohomology
import OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Geometric Cycle Class -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass

noncomputable section

/-!
# The ambient geometric class determined by fundamental-cycle traces

The actual proper trace of the regular locus is a functional on all
complementary compact-support cohomology classes. Canonical Poincare duality
and the field universal-coefficient theorem represent this functional by a
unique ordinary class on the complement of the singular boundary. The
proved absolute restriction isomorphism extends it uniquely to the ambient
projective variety.

The construction uses no supported Thom class or assumed comparison with
the existing supported cycle-class construction. Their comparison is a
separate theorem.
-/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Duality.Poincare.CompactSupportAnd

namespace DimensionCycleSupport

variable {V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The unique class on the actual regular ambient open set whose
compact-support evaluations are the proper fundamental-cycle trace. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricCycleClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of Z.regularAmbientSpace) (p + p) :=
  (Duality.Poincare.CompactSupportAnd.compactSupportDualCohomologyEquiv V.complexDimension
    (M := Z.regularAmbientSpace) (p + p) (2 * Z.regularComplexDimension)
    Z.regularGeometricTrace_degree).symm Z.regularGeometricTrace

/-- The defining characterization holds for every complementary
compact-support class, not merely classes supported in coordinate charts. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricCycleClass_evaluation (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (b : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)) :
    Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * Z.regularComplexDimension)
        Z.regularGeometricTrace_degree Z.regularGeometricCycleClass b =
      Z.regularGeometricTrace b :=
  Duality.Poincare.CompactSupportAnd.compactSupportDualCohomologyEquiv_symm_apply V.complexDimension
    (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
    Z.regularGeometricTrace b

/-- The actual field UCT and canonical cap duality prove uniqueness of
the class with the specified geometric trace on all compact-support tests. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.regularGeometricCycleClass_unique (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (p + p))
    (ha : ∀ b, Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
      (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a b =
        Z.regularGeometricTrace b) :
    a = Z.regularGeometricCycleClass := by
  apply (Duality.Poincare.CompactSupportAnd.cohomology_eq_iff_compactSupportEvaluation_eq V.complexDimension
    (p + p) (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
    a Z.regularGeometricCycleClass).mpr
  intro b
  exact (ha b).trans (Z.regularGeometricCycleClass_evaluation b).symm

/-- Equality to the regular geometric class is equivalent to its full
geometric trace characterization. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_regularGeometricCycleClass_iff (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (a : Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (p + p)) :
    a = Z.regularGeometricCycleClass ↔
      ∀ b, Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
        (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree a b =
          Z.regularGeometricTrace b := by
  constructor
  · rintro rfl
    exact Z.regularGeometricCycleClass_evaluation
  · exact Z.regularGeometricCycleClass_unique a

/-- The geometric rational class on the ambient projective variety is
the unique extension of the regular-locus trace class across the actual
singular boundary. -/
def _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    V.rationalCohomology (p + p) :=
  Z.regularAmbientCohomologyIso.inv Z.regularGeometricCycleClass

/-- Restriction of the ambient geometric class is exactly the class
represented by the proper regular-locus trace functional. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_regularRestriction (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    Z.regularAmbientCohomologyRestriction (p + p) Z.geometricCycleClass =
      Z.regularGeometricCycleClass :=
  Z.regularAmbientCohomologyIso.toLinearEquiv.apply_symm_apply Z.regularGeometricCycleClass

/-- The ambient class has the required geometric trace on every
complementary compact-support test in the regular ambient open set. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_evaluation (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (b : Duality.Poincare.CompactSupportCohomology.compactSupportedCohomology (ModuleCat.of ℚ ℚ)
      (TopCat.of Z.regularAmbientSpace) (2 * Z.regularComplexDimension)) :
    Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p) (2 * Z.regularComplexDimension)
        Z.regularGeometricTrace_degree
        (Z.regularAmbientCohomologyRestriction (p + p) Z.geometricCycleClass) b =
      Z.regularGeometricTrace b := by
  rw [Z.geometricCycleClass_regularRestriction]
  exact Z.regularGeometricCycleClass_evaluation b

/-- These actual geometric evaluations uniquely determine an ordinary
rational class on the whole projective variety. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.geometricCycleClass_unique (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (a : V.rationalCohomology (p + p))
    (ha : ∀ b, Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
      (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
        (Z.regularAmbientCohomologyRestriction (p + p) a) b =
          Z.regularGeometricTrace b) :
    a = Z.geometricCycleClass := by
  apply Z.regularAmbientCohomologyRestriction_injective
  rw [Z.geometricCycleClass_regularRestriction]
  exact Z.regularGeometricCycleClass_unique _ ha

/-- A full geometric characterization, with every compact-support test
and the actual open restriction explicit. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.eq_geometricCycleClass_iff (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p)
    (a : V.rationalCohomology (p + p)) :
    a = Z.geometricCycleClass ↔
      ∀ b, Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
        (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
          (Z.regularAmbientCohomologyRestriction (p + p) a) b =
            Z.regularGeometricTrace b := by
  constructor
  · rintro rfl
    exact Z.geometricCycleClass_evaluation
  · exact Z.geometricCycleClass_unique a

/-- Existence and uniqueness are proved from the genuine trace, UCT,
Poincare duality, and the actual singular-boundary vanishing theorem. -/
theorem _root_.OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport.existsUnique_geometricCycleClass (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) :
    ∃! a : V.rationalCohomology (p + p),
      ∀ b, Duality.Poincare.CompactSupportDualCohomology.compactSupportEvaluation V.complexDimension (p + p)
        (2 * Z.regularComplexDimension) Z.regularGeometricTrace_degree
          (Z.regularAmbientCohomologyRestriction (p + p) a) b =
            Z.regularGeometricTrace b :=
  ⟨Z.geometricCycleClass, Z.geometricCycleClass_evaluation, Z.geometricCycleClass_unique⟩

end DimensionCycleSupport

namespace IntegralProjectiveVariety

/-- Finite rational cycles act by finite rational combination of the
independently constructed geometric fundamental-cycle trace classes. -/
def _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V p →ₗ[ℚ] V.rationalCohomology (p + p) :=
  Finsupp.linearCombination ℚ (fun Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.geometricCycleClass)

@[simp]
theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    (Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p) (q : ℚ) :
    V.geometricCycleClassMap p (Finsupp.single Z q) = q • Z.geometricCycleClass :=
  Finsupp.linearCombination_single ℚ
    (v := fun Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.geometricCycleClass) q Z

theorem _root_.OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.range_geometricCycleClassMap (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    LinearMap.range (V.geometricCycleClassMap p) =
      Submodule.span ℚ (Set.range
        (fun Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.geometricCycleClass)) :=
  Finsupp.range_linearCombination ℚ
    (v := fun Z : AlgebraicGeometry.CycleClass.Geometric.DimensionCycles.DimensionCycleSupport V p => Z.geometricCycleClass)

end IntegralProjectiveVariety

end

end OAI.AlgebraicTopology.DeRham.Comparison.GeometricCycleClass
