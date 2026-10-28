import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldOpenPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapFunctionField

/-! # Field Point Factors -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FieldPointFactors

noncomputable section

/-! The common field-valued point factors compatibly through every
standard chart and double overlap. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

def projectiveCoordinateFieldPoint (i : Fin (n + 1)) :
    Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) ⟶
      (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).toScheme :=
  FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint K (X i) (X_ne_zero i) (isHomogeneous_X K i) Nat.zero_lt_one

theorem projectiveCoordinateFieldPoint_inclusion (i : Fin (n + 1)) :
    projectiveCoordinateFieldPoint K i ≫ (Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i)).ι =
      FunctionFieldPoint.projectiveFunctionFieldPoint K n :=
  (FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint_inclusion K (X i) (X_ne_zero i)
    (isHomogeneous_X K i) Nat.zero_lt_one).trans (FunctionFieldPoint.projectiveFunctionFieldPoint_coordinate K i).symm

def projectiveDoubleFieldPoint (i j : Fin (n + 1)) :
    Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) ⟶ (OverlapSectionUnits.projectiveDoubleOpen K i j).toScheme :=
  FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint K (X i * X j) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (SetLike.mul_mem_graded (isHomogeneous_X K i) (isHomogeneous_X K j)) (by decide)

theorem projectiveDoubleFieldPoint_inclusion (i j : Fin (n + 1)) :
    projectiveDoubleFieldPoint K i j ≫ (OverlapSectionUnits.projectiveDoubleOpen K i j).ι = FunctionFieldPoint.projectiveFunctionFieldPoint K n := by
  have h := FunctionFieldPoint.projectiveFunctionFieldChartPoint_awayMap K (X i) (X j) (X i * X j)
    (X_ne_zero i) (X_ne_zero j) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (isHomogeneous_X K i) (isHomogeneous_X K j) Nat.zero_lt_one rfl
  exact (FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint_inclusion K (X i * X j)
    (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (SetLike.mul_mem_graded (isHomogeneous_X K i) (isHomogeneous_X K j)) (by decide)).trans
      (h.symm.trans (FunctionFieldPoint.projectiveFunctionFieldPoint_coordinate K i).symm)

theorem projectiveDoubleFieldPoint_sections (i j : Fin (n + 1)) :
    (OverlapSectionUnits.projectiveDoubleOpen K i j).topIso.inv ≫ (projectiveDoubleFieldPoint K i j).appTop ≫
        (Scheme.ΓSpecIso (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))).hom =
      CommRingCat.ofHom (OverlapFunctionField.projectiveOverlapFunctionFieldMap K i j) :=
  FunctionFieldOpenPoint.projectiveFunctionFieldOpenPoint_sections K (X i * X j)
    (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (SetLike.mul_mem_graded (isHomogeneous_X K i) (isHomogeneous_X K j)) (by decide)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FieldPointFactors
