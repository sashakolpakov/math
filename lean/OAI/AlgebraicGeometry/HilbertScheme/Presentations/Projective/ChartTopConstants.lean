import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FieldPointFactors

/-! # Chart Top Constants -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartTopConstants

noncomputable section

/-! Field constants as actual top sections of the standard chart
structure sheaves, with their exact evaluation at the common point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

def projectiveChartTopConstants (i : Fin (n + 1)) :
    K →+* Γ((Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).toScheme, ⊤) :=
  (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).topIso.inv.hom.comp
    ((Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) (X i) (isHomogeneous_X K i) Nat.zero_lt_one).hom.hom.comp
      (Polynomial.Dehomogenization.PolynomialProjective.chartConstants i))

theorem projectiveCoordinateFieldPoint_constant (i : Fin (n + 1)) (c : K) :
    (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
      ((FieldPointFactors.projectiveCoordinateFieldPoint K i).appTop (projectiveChartTopConstants K i c)) =
        algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (C c) := by
  let b := Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) (X i) (isHomogeneous_X K i) Nat.zero_lt_one
  have h := congrArg (fun f : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n),
      Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)) ⟶
        CommRingCat.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) =>
          f (b.hom (Polynomial.Dehomogenization.PolynomialProjective.chartConstants i c)))
    (FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint_sections K (X i) (X_ne_zero i) (isHomogeneous_X K i) Nat.zero_lt_one)
  change (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom
      ((FieldPointFactors.projectiveCoordinateFieldPoint K i).appTop (projectiveChartTopConstants K i c)) =
        Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K (X i) (X_ne_zero i) (b.inv (b.hom (Polynomial.Dehomogenization.PolynomialProjective.chartConstants i c))) at h
  rw [Iso.hom_inv_id_apply] at h
  exact h.trans (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap_constant K i c)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartTopConstants
