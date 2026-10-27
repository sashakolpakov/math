/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import Mathlib
import SphericalReggeScissors.PhaseAction

/-!
# Algebra of the orientation conic and fixed-phase cover

This file checks the polynomial identities behind the two rational charts
and the residual quadratic cover.  Scheme-theoretic assertions (finite
etaleness after the displayed discriminant is inverted) are deliberately
kept in the external geometric interface; their entire coordinate algebra
is checked here.
-/

namespace SphericalReggeScissors

section Coefficients

variable {R : Type*} [CommRing R]

/-- The coefficient `B` in the determinant quadratic. -/
def determinantB (A B C D y : R) : R :=
  2 * (A * B + D * C - y * (A * C + D * B))

/-- The constant coefficient `C` in the determinant quadratic. -/
def determinantC (A B C D y : R) : R :=
  1 - A ^ 2 - B ^ 2 - C ^ 2 - D ^ 2 - y ^ 2 +
    2 * y * (A * D + B * C) + (A * C - B * D) ^ 2

/-- The determinant polynomial in the descended coordinate `x`. -/
def determinantQuadratic (s B C x : R) : R := s ^ 2 * x ^ 2 + B * x + C

/-- The universal symmetric Gram matrix in the manuscript's edge order. -/
def gramMatrix (x A B y C D : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, x, A, D;
     x, 1, B, C;
     A, B, 1, y;
     D, C, y, 1]

/-- Direct expansion of the `4 × 4` Gram determinant.  This is the
quadratic-in-`x` calculation preceding the rational orientation charts. -/
theorem gramMatrix_det (x A B y C D : R) :
    (gramMatrix x A B y C D).det =
      -(1 - y ^ 2) * x ^ 2 + determinantB A B C D y * x +
        determinantC A B C D y := by
  rw [Matrix.det_succ_row_zero]
  simp [gramMatrix, Matrix.det_fin_three, Fin.sum_univ_succ,
    Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc,
    determinantB, determinantC]
  ring

/-- After choosing `s` with `1-y²=-s²`, the preceding determinant is
exactly the displayed conic equation. -/
theorem gramMatrix_det_quadratic {x A B y C D s : R}
    (hys : 1 - y ^ 2 = -(s ^ 2)) :
    (gramMatrix x A B y C D).det =
      determinantQuadratic s (determinantB A B C D y)
        (determinantC A B C D y) x := by
  rw [gramMatrix_det, hys]
  simp only [determinantQuadratic]
  ring

end Coefficients

section RetainedPhase

variable {K : Type*} [Field K] [CharZero K]

/-- The two Laurent coordinates attached to the retained phase `q`. -/
def qSkew (q : K) : K := (q - q⁻¹) / 2
def qGram (q : K) : K := -(q + q⁻¹) / 2

/-- The manuscript's identity `1 - y² = -s²`. -/
theorem qGram_qSkew_relation {q : K} (hq : q ≠ 0) :
    1 - qGram q ^ 2 = -(qSkew q) ^ 2 := by
  unfold qGram qSkew
  field_simp [hq]
  ring

end RetainedPhase

section ReggeCoefficients

variable {K : Type*} [Field K]

/-- Elimination of the fourth moving phase on the phase hypersurface. -/
def eliminatedFourthPhase (a b c tau : K) : K := tau ^ 2 / (a * b * c)

/-- The eliminated coordinates satisfy `abcd = τ²`. -/
theorem eliminatedFourthPhase_relation {a b c tau : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a * b * c * eliminatedFourthPhase a b c tau = tau ^ 2 := by
  unfold eliminatedFourthPhase
  field_simp [ha, hb, hc]

/-- Exact Laurent-polynomial verification that the linear coefficient of
the Gram determinant is fixed by the monomial Regge substitution. -/
theorem determinantB_regge_invariant {a b c tau q : K}
    [CharZero K] (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ht : tau ≠ 0) (hq : q ≠ 0) :
    let d := eliminatedFourthPhase a b c tau
    determinantB (gramEntry a) (gramEntry b) (gramEntry c) (gramEntry d) (gramEntry q) =
      determinantB (gramEntry (tau / a)) (gramEntry (tau / b))
        (gramEntry (tau / c)) (gramEntry (tau / d)) (gramEntry q) := by
  dsimp [eliminatedFourthPhase, determinantB, gramEntry]
  field_simp [ha, hb, hc, ht, hq]
  ring

/-- Exact Laurent-polynomial verification that the constant coefficient of
the Gram determinant is fixed by the monomial Regge substitution. -/
theorem determinantC_regge_invariant {a b c tau q : K}
    [CharZero K] (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ht : tau ≠ 0) (hq : q ≠ 0) :
    let d := eliminatedFourthPhase a b c tau
    determinantC (gramEntry a) (gramEntry b) (gramEntry c) (gramEntry d) (gramEntry q) =
      determinantC (gramEntry (tau / a)) (gramEntry (tau / b))
        (gramEntry (tau / c)) (gramEntry (tau / d)) (gramEntry q) := by
  dsimp [eliminatedFourthPhase, determinantC, gramEntry]
  field_simp [ha, hb, hc, ht, hq]
  ring

end ReggeCoefficients

section BinaryQuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- A symmetric binary form and the standard alternating matrix used in
the Schur-complement splitting argument. -/
def symmetricBinaryMatrix (a b d : R) : Matrix (Fin 2) (Fin 2) R := !![a, b; b, d]

def alternatingBinaryMatrix : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- For every symmetric binary matrix `C`, `(J₀ C)² = -det(C) I`. -/
theorem alternating_mul_symmetric_square (a b d : R) :
    (alternatingBinaryMatrix * symmetricBinaryMatrix a b d) *
        (alternatingBinaryMatrix * symmetricBinaryMatrix a b d) =
      -(symmetricBinaryMatrix a b d).det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alternatingBinaryMatrix, symmetricBinaryMatrix, Matrix.mul_apply,
      Matrix.det_fin_two, Fin.sum_univ_succ] <;> ring

/-- The same matrix is skew-adjoint for `C`: `(J₀C)ᵗC + C(J₀C)=0`. -/
theorem alternating_mul_symmetric_skew_adjoint (a b d : R) :
    (alternatingBinaryMatrix * symmetricBinaryMatrix a b d).transpose *
          symmetricBinaryMatrix a b d +
        symmetricBinaryMatrix a b d *
          (alternatingBinaryMatrix * symmetricBinaryMatrix a b d) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [alternatingBinaryMatrix, symmetricBinaryMatrix, Matrix.mul_apply,
      Fin.sum_univ_succ]

end BinaryQuadraticAlgebra

section BinaryQuadraticField

variable {K : Type*} [Field K]

/-- The normalized operator `J=t⁻¹J₀C` from the manuscript. -/
def normalizedBinaryInvolution (t a b d : K) : Matrix (Fin 2) (Fin 2) K :=
  t⁻¹ • (alternatingBinaryMatrix * symmetricBinaryMatrix a b d)

/-- If `det C = -t²`, normalization turns the preceding square identity
into `J²=I`. -/
theorem normalizedBinaryInvolution_square {t a b d : K} (ht : t ≠ 0)
    (hdet : (symmetricBinaryMatrix a b d).det = -(t ^ 2)) :
    normalizedBinaryInvolution t a b d * normalizedBinaryInvolution t a b d = 1 := by
  have hh : a * d - b ^ 2 + t ^ 2 = 0 := by
    simp [symmetricBinaryMatrix, Matrix.det_fin_two] at hdet
    linear_combination hdet
  have hdiag : b ^ 2 - a * d = t ^ 2 := by
    linear_combination -hh
  ext i j
  fin_cases i
  · fin_cases j
    · simp [normalizedBinaryInvolution, alternatingBinaryMatrix, symmetricBinaryMatrix,
        Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_succ] at hdet ⊢
      field_simp [ht] at hdet ⊢
      simpa [sub_eq_add_neg, add_comm, mul_comm] using hdiag
    · simp [normalizedBinaryInvolution, alternatingBinaryMatrix, symmetricBinaryMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ]
      ring
  · fin_cases j
    · simp [normalizedBinaryInvolution, alternatingBinaryMatrix, symmetricBinaryMatrix,
        Matrix.mul_apply, Fin.sum_univ_succ]
      ring
    · simp [normalizedBinaryInvolution, alternatingBinaryMatrix, symmetricBinaryMatrix,
        Matrix.mul_apply, Matrix.det_fin_two, Fin.sum_univ_succ] at hdet ⊢
      field_simp [ht] at hdet ⊢
      simpa [sub_eq_add_neg, add_comm, mul_comm] using hdiag

/-- The phase vector `(1,u)` is isotropic for the binary Gram block with
off-diagonal entry `-(u+u⁻¹)/2`. -/
theorem phase_vector_isotropic [CharZero K] {u : K} (hu : u ≠ 0) :
    1 + 2 * gramEntry u * u + u ^ 2 = 0 := by
  unfold gramEntry
  field_simp [hu]
  ring

end BinaryQuadraticField

section Charts

variable {K : Type*} [Field K]

/-- The minus-chart coordinate `r = w - sx`. -/
def minusChartCoordinate (s x w : K) : K := w - s * x

/-- The plus-chart coordinate `r₊ = w + sx`. -/
def plusChartCoordinate (s x w : K) : K := w + s * x

/-- Substitution of `w = r + sx` cancels the quadratic term. -/
theorem minus_chart_linearization {s B C x w : K}
    (h : w ^ 2 = determinantQuadratic s B C x) :
    (2 * s * minusChartCoordinate s x w - B) * x =
      C - minusChartCoordinate s x w ^ 2 := by
  dsimp [minusChartCoordinate, determinantQuadratic] at h ⊢
  linear_combination h

/-- Conversely, the linear minus-chart equation reconstructs the conic. -/
theorem minus_chart_reconstruct {s B C x r : K}
    (h : (2 * s * r - B) * x = C - r ^ 2) :
    (r + s * x) ^ 2 = determinantQuadratic s B C x := by
  dsimp [determinantQuadratic]
  linear_combination h

/-- The explicit rational formula on the minus chart. -/
theorem minus_chart_formula {s B C x w : K}
    (hconic : w ^ 2 = determinantQuadratic s B C x)
    (hden : 2 * s * minusChartCoordinate s x w - B ≠ 0) :
    x = (C - minusChartCoordinate s x w ^ 2) /
      (2 * s * minusChartCoordinate s x w - B) := by
  apply (eq_div_iff hden).2
  simpa [mul_comm] using minus_chart_linearization hconic

/-- Substitution of `w = r₊ - sx` cancels the quadratic term. -/
theorem plus_chart_linearization {s B C x w : K}
    (h : w ^ 2 = determinantQuadratic s B C x) :
    (-2 * s * plusChartCoordinate s x w - B) * x =
      C - plusChartCoordinate s x w ^ 2 := by
  dsimp [plusChartCoordinate, determinantQuadratic] at h ⊢
  linear_combination h

/-- Conversely, the linear plus-chart equation reconstructs the conic. -/
theorem plus_chart_reconstruct {s B C x r : K}
    (h : (-2 * s * r - B) * x = C - r ^ 2) :
    (r - s * x) ^ 2 = determinantQuadratic s B C x := by
  dsimp [determinantQuadratic]
  linear_combination h

/-- The explicit rational formula on the plus chart. -/
theorem plus_chart_formula {s B C x w : K}
    (hconic : w ^ 2 = determinantQuadratic s B C x)
    (hden : -2 * s * plusChartCoordinate s x w - B ≠ 0) :
    x = (C - plusChartCoordinate s x w ^ 2) /
      (-2 * s * plusChartCoordinate s x w - B) := by
  apply (eq_div_iff hden).2
  simpa [mul_comm] using plus_chart_linearization hconic

/-- If both chart denominators vanish then `4sw = 0`. -/
theorem both_chart_denominators_force_four_sw {s B x w : K}
    (hminus : 2 * s * minusChartCoordinate s x w - B = 0)
    (hplus : -2 * s * plusChartCoordinate s x w - B = 0) :
    4 * s * w = 0 := by
  dsimp [minusChartCoordinate, plusChartCoordinate] at hminus hplus
  linear_combination hminus - hplus

/-- Hence the two rational charts cover the locus `sw ≠ 0`. -/
theorem chart_cover [CharZero K] {s B x w : K} (hs : s ≠ 0) (hw : w ≠ 0) :
    2 * s * minusChartCoordinate s x w - B ≠ 0 ∨
      -2 * s * plusChartCoordinate s x w - B ≠ 0 := by
  by_contra h
  push Not at h
  have hfour := both_chart_denominators_force_four_sw h.1 h.2
  exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hw hfour

end Charts

section FixedPhase

variable {K : Type*} [Field K]

/-- The monic polynomial defining the residual fixed-phase cover. -/
def fixedPhasePolynomial (x p : K) : K := p ^ 2 + 2 * x * p + 1

/-- Its discriminant is `4(x² - 1)`. -/
theorem fixedPhase_discriminant (x : K) :
    (2 * x) ^ 2 - 4 = 4 * (x ^ 2 - 1) := by ring

/-- A root of the fixed-phase polynomial is automatically a unit. -/
theorem fixedPhase_ne_zero {x p : K} (hp : fixedPhasePolynomial x p = 0) : p ≠ 0 := by
  intro hp0
  simp [fixedPhasePolynomial, hp0] at hp

/-- The nontrivial deck formula agrees with inversion. -/
theorem fixedPhase_inv_eq_deck {x p : K} (hp : fixedPhasePolynomial x p = 0) :
    p⁻¹ = -2 * x - p := by
  have hp0 := fixedPhase_ne_zero hp
  dsimp [fixedPhasePolynomial] at hp
  field_simp [hp0]
  linear_combination hp

/-- The affine deck formula is an involution. -/
theorem fixedPhase_deck_involutive (x p : K) :
    -2 * x - (-2 * x - p) = p := by ring

/-- The deck transformation carries roots to roots. -/
theorem fixedPhase_deck_preserves_root {x p : K}
    (hp : fixedPhasePolynomial x p = 0) :
    fixedPhasePolynomial x (-2 * x - p) = 0 := by
  dsimp [fixedPhasePolynomial] at hp ⊢
  linear_combination hp

/-- The two roots have product one. -/
theorem fixedPhase_root_times_deck {x p : K}
    (hp : fixedPhasePolynomial x p = 0) :
    p * (-2 * x - p) = 1 := by
  dsimp [fixedPhasePolynomial] at hp
  linear_combination -hp

end FixedPhase

end SphericalReggeScissors
