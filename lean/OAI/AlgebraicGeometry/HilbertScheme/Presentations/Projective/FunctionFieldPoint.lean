import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FunctionFieldRestrictions
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Function Field Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldPoint

noncomputable section

/-! The canonical function-field-valued point of projective space
is independent of the standard chart used to construct it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ}

theorem homogeneousChartFunctionFieldMap_awayMap_of_eq
    (f g x : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) (hg : g ≠ 0) (hx0 : x ≠ 0)
    {d : ℕ} (hgd : g ∈ Hilbert.Polynomial.GradedHilbert.grading K n d) (hx : x = f * g) :
    (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K x hx0).comp
      (HomogeneousLocalization.awayMap (Hilbert.Polynomial.GradedHilbert.grading K n) hgd hx) =
        Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf := by
  subst x
  exact Homogeneous.FunctionFieldRestrictions.homogeneousChartFunctionFieldMap_awayMap K f g hf hg hgd

def projectiveFunctionFieldChartPoint (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0)
    {d : ℕ} (hfd : f ∈ Hilbert.Polynomial.GradedHilbert.grading K n d) (hd : 0 < d) :
    Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  Spec.map (CommRingCat.ofHom (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf)) ≫
    Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd

theorem projectiveFunctionFieldChartPoint_awayMap
    (f g x : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (hf : f ≠ 0) (hg : g ≠ 0) (hx0 : x ≠ 0)
    {d e : ℕ} (hfd : f ∈ Hilbert.Polynomial.GradedHilbert.grading K n d) (hgd : g ∈ Hilbert.Polynomial.GradedHilbert.grading K n e)
    (hd : 0 < d) (hx : x = f * g) :
    projectiveFunctionFieldChartPoint K f hf hfd hd =
      projectiveFunctionFieldChartPoint K x hx0 (hx ▸ SetLike.mul_mem_graded hfd hgd)
        (hd.trans_le (d.le_add_right e)) := by
  have ha := homogeneousChartFunctionFieldMap_awayMap_of_eq K f g x hf hg hx0 hgd hx
  change Spec.map (CommRingCat.ofHom (Homogeneous.ChartFunctionField.homogeneousChartFunctionFieldMap K f hf)) ≫
    Proj.awayι (Hilbert.Polynomial.GradedHilbert.grading K n) f hfd hd = _
  rw [← ha, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]
  rfl

theorem projectiveFunctionFieldChartPoint_coordinate_eq (i j : Fin (n + 1)) :
    projectiveFunctionFieldChartPoint K (X i) (X_ne_zero i) (isHomogeneous_X K i) Nat.zero_lt_one =
      projectiveFunctionFieldChartPoint K (X j) (X_ne_zero j) (isHomogeneous_X K j) Nat.zero_lt_one := by
  have hi := projectiveFunctionFieldChartPoint_awayMap K (X i) (X j) (X i * X j)
    (X_ne_zero i) (X_ne_zero j) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (isHomogeneous_X K i) (isHomogeneous_X K j) Nat.zero_lt_one rfl
  have hj := projectiveFunctionFieldChartPoint_awayMap K (X j) (X i) (X i * X j)
    (X_ne_zero j) (X_ne_zero i) (mul_ne_zero (X_ne_zero i) (X_ne_zero j))
    (isHomogeneous_X K j) (isHomogeneous_X K i) Nat.zero_lt_one (mul_comm _ _)
  exact hi.trans hj.symm

def projectiveFunctionFieldPoint (n : ℕ) :
    Spec (.of (FractionRing (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading K n) :=
  projectiveFunctionFieldChartPoint K (X 0) (X_ne_zero 0) (isHomogeneous_X K 0) Nat.zero_lt_one

theorem projectiveFunctionFieldPoint_coordinate (i : Fin (n + 1)) :
    projectiveFunctionFieldPoint K n =
      projectiveFunctionFieldChartPoint K (X i) (X_ne_zero i) (isHomogeneous_X K i) Nat.zero_lt_one :=
  projectiveFunctionFieldChartPoint_coordinate_eq K 0 i

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FunctionFieldPoint
