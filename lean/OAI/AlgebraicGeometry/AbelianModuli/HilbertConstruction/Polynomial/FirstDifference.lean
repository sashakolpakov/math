import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # First Difference -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.FirstDifference

noncomputable section

/-! The first difference lowers the degree of every nonconstant rational polynomial. Substitution by a nonzero dilation preserves degree. These operations describe the actual Euler polynomial after passing to a positive line-bundle power and taking a regular-section cokernel. -/
open _root_.Polynomial

def polynomialFirstDifference (P : Polynomial ℚ) : Polynomial ℚ := P.comp (X + C 1) - P

theorem polynomialFirstDifference_eval (P : Polynomial ℚ) (x : ℚ) :
    (polynomialFirstDifference P).eval x = P.eval (x + 1) - P.eval x := by
  simp [polynomialFirstDifference]

theorem polynomialFirstDifference_eq_zero_of_natDegree_zero
    (P : Polynomial ℚ) (hP : P.natDegree = 0) : polynomialFirstDifference P = 0 := by
  have he := eq_C_of_natDegree_eq_zero hP
  rw [he]
  simp [polynomialFirstDifference]

theorem polynomialFirstDifference_natDegree_lt
    (P : Polynomial ℚ) (hP : 0 < P.natDegree) :
    (polynomialFirstDifference P).natDegree < P.natDegree := by
  have hcomp : (P.comp (X + C 1)).natDegree = P.natDegree := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one]
  have hlead : (P.comp (X + C 1)).leadingCoeff = P.leadingCoeff := by
    rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
      leadingCoeff_X_add_C, one_pow, mul_one]
  have hcoeff : (P.comp (X + C 1)).coeff P.natDegree = P.coeff P.natDegree := by
    calc
      (P.comp (X + C 1)).coeff P.natDegree =
          (P.comp (X + C 1)).coeff (P.comp (X + C 1)).natDegree :=
        congrArg (P.comp (X + C 1)).coeff hcomp.symm
      _ = (P.comp (X + C 1)).leadingCoeff := rfl
      _ = P.leadingCoeff := hlead
      _ = P.coeff P.natDegree := rfl
  have htop : (polynomialFirstDifference P).coeff P.natDegree = 0 := by
    rw [polynomialFirstDifference, coeff_sub, hcoeff, sub_self]
  have hle : (polynomialFirstDifference P).natDegree ≤ P.natDegree := by
    exact (natDegree_sub_le _ _).trans (by rw [hcomp, max_self])
  apply lt_of_le_of_ne hle
  intro heq
  have hz : polynomialFirstDifference P = 0 := leadingCoeff_eq_zero.mp (by
    change (polynomialFirstDifference P).coeff (polynomialFirstDifference P).natDegree = 0
    rw [heq]
    exact htop)
  rw [hz, natDegree_zero] at heq
  exact (Nat.ne_of_gt hP) heq.symm

theorem polynomial_nonzero_dilation_natDegree (P : Polynomial ℚ) (d : ℚ) (hd : d ≠ 0) :
    (P.comp (C d * X)).natDegree = P.natDegree := by
  rw [natDegree_comp, natDegree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hd), natDegree_X, mul_one]

theorem polynomialFirstDifference_dilation_natDegree_lt
    (P : Polynomial ℚ) (hP : 0 < P.natDegree) (d : ℚ) (hd : d ≠ 0) :
    (polynomialFirstDifference (P.comp (C d * X))).natDegree < P.natDegree := by
  have hD := polynomial_nonzero_dilation_natDegree P d hd
  exact (polynomialFirstDifference_natDegree_lt (P.comp (C d * X)) (hD.symm ▸ hP)).trans_eq hD

theorem polynomialFirstDifference_dilation_eval (P : Polynomial ℚ) (d x : ℚ) :
    (polynomialFirstDifference (P.comp (C d * X))).eval x =
      P.eval (d * (x + 1)) - P.eval (d * x) := by
  simp [polynomialFirstDifference]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.FirstDifference
