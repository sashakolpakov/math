import OAI.AlgebraicGeometry.Hodge.FiltrationId
import OAI.AlgebraicGeometry.Cohomology.SingularComparison

/-! # Singular Sheaf Comparison -/

namespace OAI.AlgebraicGeometry

noncomputable section

open scoped OAI.AlgebraicGeometry.Hodge.Filtration.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Singular and constant-sheaf comparison

On the analytic space of a smooth complex scheme, the rational constant sheaf is resolved by
the sheafified rational singular-cochain complex. Localizing at quasi-isomorphisms gives a
canonical comparison equivalence in every cohomological degree.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.ComplexPoint.Basic.Point

variable (X : Over (Spec ↧ℂ))

/-- The rational constant-sheaf comparison with the integer-indexed singular-cochain
resolution. -/
def ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt :
    ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X ⟶
      ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ :=
  ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X ℚ

/-- The rational constant-to-singular comparison is a quasi-isomorphism on a smooth
complex-point space. -/
lemma ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom] :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) := by
  exact ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso X ℚ

/-- Hypercohomology of the integer-indexed rational singular-cochain sheaf complex. -/
abbrev ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology (n : ℤ) : Type 1 :=
  ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X ℚ) n

/-- Hypercohomology of the rational constant sheaf complex is canonically additively equivalent
to the hypercohomology of its singular-cochain resolution. -/
def ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ) :
    ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) n ≃+
      ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology X n where
  toEquiv := Localization.SmallShiftedHom.postcompEquiv
    (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X)
    (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt_quasiIso X)
  map_add' α β :=
    (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
      (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n).map_add α β

@[simp]
lemma ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℤ)
    (α : ComplexPoint.Basic.ComplexSchemePoint.Hypercohomology X (ComplexPoint.Basic.ComplexSchemePoint.constantFieldSheafComplexInt ℚ X) n) :
    ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv X n α =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X
        (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n α :=
  rfl

/-- Rational constant-sheaf cohomology is canonically additively equivalent to the
hypercohomology of its singular-cochain resolution. -/
def ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) :
    H^n(X; ℚ) ≃+ ComplexPoint.Basic.ComplexSchemePoint.RationalSingularCochainHypercohomology X n :=
  (ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm.trans
    (ComplexPoint.Basic.ComplexSchemePoint.rationalHypercohomologySingularCochainAddEquiv X n)

@[simp]
lemma ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv_apply
    [IsIntegral X.left] [Smooth X.hom] (n : ℕ) (α : H^n(X; ℚ)) :
    ComplexPoint.Basic.ComplexSchemePoint.rationalCohomologySingularCochainAddEquiv X n α =
      ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyMap X (ComplexPoint.Basic.ComplexSchemePoint.rationalToSingularCochainComplexInt X) n
        ((ComplexPoint.Basic.ComplexSchemePoint.hypercohomologyAddEquivConstantCohomology ℚ X n).symm α) :=
  rfl

end

end OAI.AlgebraicGeometry
