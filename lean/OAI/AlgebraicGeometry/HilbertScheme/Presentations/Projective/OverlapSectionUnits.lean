import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.DoubleChartUnits
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-! # Overlap Section Units -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapSectionUnits

noncomputable section

/-! Scalar-power descriptions hold for actual invertible regular
sections on the intersection of two standard projective opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (K : Type u) [Field K] {n : ℕ} (i j : Fin (n + 1))

def projectiveDoubleOpen : (Proj (Hilbert.Polynomial.GradedHilbert.grading K n)).Opens :=
  Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i * X j)

theorem projectiveDoubleOpen_eq_inf : projectiveDoubleOpen K i j =
    Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X i) ⊓
      Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading K n) (X j) :=
  Proj.basicOpen_mul _ _ _

def projectiveDoubleSectionIso : CommRingCat.of (DoubleChartUnits.ProjectiveDoubleChartRing K i j) ≅
    Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), projectiveDoubleOpen K i j) :=
  Proj.basicOpenIsoAway (Hilbert.Polynomial.GradedHilbert.grading K n) (X i * X j)
    ((isHomogeneous_X K i).mul (isHomogeneous_X K j)) (by decide)

def projectiveOverlapRatio : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), projectiveDoubleOpen K i j) :=
  (projectiveDoubleSectionIso K i j).hom (DoubleChartUnits.projectiveDoubleChartRatio K i j)

def projectiveOverlapConstant (c : K) : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), projectiveDoubleOpen K i j) :=
  (projectiveDoubleSectionIso K i j).hom (DoubleChartUnits.projectiveDoubleChartConstant K i j c)

theorem projectiveOverlap_unit_powers (hji : j ≠ i)
    (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), projectiveDoubleOpen K i j)ˣ) :
    ∃ (c : Kˣ) (a b : ℕ), (z : Γ(Proj (Hilbert.Polynomial.GradedHilbert.grading K n), projectiveDoubleOpen K i j)) *
      projectiveOverlapRatio K i j ^ b = projectiveOverlapConstant K i j (c : K) *
        projectiveOverlapRatio K i j ^ a := by
  let e := (projectiveDoubleSectionIso K i j).commRingCatIsoToRingEquiv
  let z' : (DoubleChartUnits.ProjectiveDoubleChartRing K i j)ˣ := Units.map e.symm.toMonoidHom z
  obtain ⟨c, a, b, h⟩ := DoubleChartUnits.projectiveDoubleChart_unit_powers K i j hji z'
  have hv : e (z' : DoubleChartUnits.ProjectiveDoubleChartRing K i j) = z := e.apply_symm_apply _
  refine ⟨c, a, b, ?_⟩
  have he := congrArg e h
  rw [map_mul, map_pow, hv, map_mul, map_pow] at he
  exact he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.OverlapSectionUnits
