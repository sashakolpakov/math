import OAI.AlgebraicGeometry.Cycle.FundamentalClass
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Cycle Class Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleClassMap

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

/-! # Finite rational combinations of the unchanged Paul-Lez component classes

This map uses the original supported-cohomology construction and the original
scheme-point codimension. Its range is exactly the original challenge's span.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

/-- The original integral cycle components of the required codimension. -/
abbrev OriginalCycleComponent (p : ℕ) := {x : X.left // Order.coheight x = p}

/-- The unchanged, complex-orientation-normalized supported component class. -/
def originalCycleComponentClass (p : ℕ) (x : OriginalCycleComponent X p) :
    H^(2 * p)(X; ℚ) := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X x.val x.property

/-- Finite rational cycles, evaluated using the original component classes. -/
def originalCycleClassMap (p : ℕ) :
    (OriginalCycleComponent X p →₀ ℚ) →ₗ[ℚ] H^(2 * p)(X; ℚ) :=
  Finsupp.linearCombination ℚ (originalCycleComponentClass X p)

/-- The challenge's algebraic span is the span of precisely these original generators. -/
theorem originalCycleClassSpan_eq_span (p : ℕ) :
    ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p =
      Submodule.span ℚ (Set.range (originalCycleComponentClass X p)) := by
  apply le_antisymm
  · apply sSup_le
    rintro S ⟨x, hx, rfl⟩
    apply Submodule.span_le.mpr
    rintro a (rfl : a = ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X x hx)
    exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro a ⟨x, rfl⟩
    apply (le_sSup (show Submodule.span ℚ {ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X x.val x.property} ∈
      {Submodule.span ℚ {ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSheafClass X y hy} |
        (y : X.left) (hy : Order.coheight y = p)} from ⟨x.val, x.property, rfl⟩))
    exact Submodule.subset_span rfl

/-- The original algebraic span is the range of actual finite rational cycles. -/
theorem range_originalCycleClassMap (p : ℕ) :
    LinearMap.range (originalCycleClassMap X p) = ComplexPoint.Basic.ComplexSchemePoint.algebraicCycleClassSpan X p := by
  rw [originalCycleClassSpan_eq_span]
  exact Finsupp.range_linearCombination ℚ (v := originalCycleComponentClass X p)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CycleClassMap
