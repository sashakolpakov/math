import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic.NoncommRing

/-! # CM Symplectic Siegel -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM

/-!
# Symplectic block identities for the Siegel transformation

The blocks belong to an actual matrix in mathlib's symplectic group.
Their identities imply symmetry of the fractional transformation and
the difference formula used for its imaginary part. Invertibility of
the denominator is explicit here; its deduction from Siegel positivity
is a separate step.
-/

open scoped _root_.Matrix
open _root_.Matrix

variable (ι R : Type*) [Fintype ι] [DecidableEq ι] [CommRing R]

structure SymplecticBlocks where
  A : Matrix ι ι R
  B : Matrix ι ι R
  C : Matrix ι ι R
  D : Matrix ι ι R
  symplectic : Matrix.fromBlocks A B C D ∈ Matrix.symplecticGroup ι R

namespace SymplecticBlocks

variable {ι R} (g : SymplecticBlocks ι R)

theorem ac : g.Aᵀ * g.C = g.Cᵀ * g.A :=
  (SymplecticGroup.fromBlocks_mem_iff.mp g.symplectic).1

theorem bd : g.Bᵀ * g.D = g.Dᵀ * g.B :=
  (SymplecticGroup.fromBlocks_mem_iff.mp g.symplectic).2.1

theorem ad_cb : g.Aᵀ * g.D - g.Cᵀ * g.B = 1 :=
  (SymplecticGroup.fromBlocks_mem_iff.mp g.symplectic).2.2

theorem da_bc : g.Dᵀ * g.A - g.Bᵀ * g.C = 1 := by
  have h := congrArg Matrix.transpose g.ad_cb
  simpa only [transpose_sub, transpose_mul, transpose_transpose, transpose_one] using h

theorem cd : g.C * g.Dᵀ = g.D * g.Cᵀ := by
  have h := SymplecticGroup.transpose_mem g.symplectic
  rw [fromBlocks_transpose] at h
  simpa only [transpose_transpose] using (SymplecticGroup.fromBlocks_mem_iff.mp h).2.1

def numerator (Z : Matrix ι ι R) : Matrix ι ι R := g.A * Z + g.B

def denominator (Z : Matrix ι ι R) : Matrix ι ι R := g.C * Z + g.D

def fractional (Z : Matrix ι ι R) : Matrix ι ι R := g.numerator Z * (g.denominator Z)⁻¹

/-- The basic symplectic identity before taking any inverses. -/
theorem cross_difference (Z W : Matrix ι ι R) (hW : W.IsSymm) :
    (g.denominator W)ᵀ * g.numerator Z - (g.numerator W)ᵀ * g.denominator Z = Z - W := by
  have had : g.Cᵀ * g.B - g.Aᵀ * g.D = -1 := by
    rw [← neg_sub, g.ad_cb]
  calc
    _ = W * (g.Cᵀ * g.A - g.Aᵀ * g.C) * Z +
        W * (g.Cᵀ * g.B - g.Aᵀ * g.D) +
        (g.Dᵀ * g.A - g.Bᵀ * g.C) * Z + (g.Dᵀ * g.B - g.Bᵀ * g.D) := by
      simp only [SymplecticBlocks.denominator, SymplecticBlocks.numerator, transpose_add, transpose_mul, hW.eq]
      noncomm_ring
    _ = _ := by
      rw [g.ac, g.bd, sub_self, sub_self, had, g.da_bc]
      simp [sub_eq_add_neg, add_comm]

theorem cross_symmetric (Z : Matrix ι ι R) (hZ : Z.IsSymm) :
    (g.denominator Z)ᵀ * g.numerator Z = (g.numerator Z)ᵀ * g.denominator Z := by
  have h := g.cross_difference Z Z hZ
  rw [sub_self] at h
  exact sub_eq_zero.mp h

theorem fractional_mul_denominator (Z : Matrix ι ι R)
    (hJ : IsUnit (g.denominator Z).det) :
    g.fractional Z * g.denominator Z = g.numerator Z := by
  exact Matrix.nonsing_inv_mul_cancel_right _ _ hJ

theorem fractional_symmetric (Z : Matrix ι ι R) (hZ : Z.IsSymm)
    (hJ : IsUnit (g.denominator Z).det) : (g.fractional Z).IsSymm := by
  change (g.numerator Z * (g.denominator Z)⁻¹)ᵀ = g.numerator Z * (g.denominator Z)⁻¹
  rw [transpose_mul, transpose_nonsing_inv]
  calc
    _ = (g.denominator Z)ᵀ⁻¹ * ((g.numerator Z)ᵀ * g.denominator Z) *
        (g.denominator Z)⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.mul_one]
    _ = (g.denominator Z)ᵀ⁻¹ * ((g.denominator Z)ᵀ * g.numerator Z) *
        (g.denominator Z)⁻¹ := by rw [g.cross_symmetric Z hZ]
    _ = _ := by
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ (Matrix.isUnit_det_transpose _ hJ)]

theorem denominator_mul_transpose_C (Z : Matrix ι ι R) (hZ : Z.IsSymm) :
    g.denominator Z * g.Cᵀ = g.C * (g.denominator Z)ᵀ := by
  simp only [SymplecticBlocks.denominator, transpose_add, transpose_mul, hZ.eq, Matrix.add_mul, Matrix.mul_add]
  rw [g.cd]
  noncomm_ring

/-- The quadratic correction matrix `J⁻¹ C` is symmetric. -/
theorem correction_symmetric (Z : Matrix ι ι R) (hZ : Z.IsSymm)
    (hJ : IsUnit (g.denominator Z).det) : ((g.denominator Z)⁻¹ * g.C).IsSymm := by
  change ((g.denominator Z)⁻¹ * g.C)ᵀ = (g.denominator Z)⁻¹ * g.C
  rw [transpose_mul, transpose_nonsing_inv]
  calc
    _ = (g.denominator Z)⁻¹ * (g.denominator Z * g.Cᵀ) * (g.denominator Z)ᵀ⁻¹ := by
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ]
    _ = (g.denominator Z)⁻¹ * (g.C * (g.denominator Z)ᵀ) * (g.denominator Z)ᵀ⁻¹ := by
      rw [g.denominator_mul_transpose_C Z hZ]
    _ = _ := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_transpose _ hJ), Matrix.mul_one]

/-- The difference formula whose conjugate specialization gives the
imaginary-part transformation. -/
theorem fractional_difference (Z W : Matrix ι ι R) (hW : W.IsSymm)
    (hJZ : IsUnit (g.denominator Z).det) (hJW : IsUnit (g.denominator W).det) :
    (g.denominator W)ᵀ * (g.fractional Z - g.fractional W) * g.denominator Z = Z - W := by
  have hleft : (g.denominator W)ᵀ * g.fractional W = (g.numerator W)ᵀ := by
    have h := congrArg Matrix.transpose (g.fractional_mul_denominator W hJW)
    simpa only [transpose_mul, (g.fractional_symmetric W hW hJW).eq] using h
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, g.fractional_mul_denominator Z hJZ, hleft]
  exact g.cross_difference Z W hW

end SymplecticBlocks

end AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM

namespace AlgebraicGeometry.ComplexMultiplication

/-!
# Imaginary parts under real symplectic substitutions

Real symplectic blocks are included in the complex matrices. The general
difference formula specializes to the exact imaginary-part identity. The
denominator's determinant is required to be a unit; no assertion about
theta functions or their inputs is assumed in these matrix calculations.
-/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CMSymplecticSiegel.CM.matrixConjugate (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := M.map (starRingEnd ℂ)

def CMSymplecticSiegel.CM.matrixImaginary (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := M.map (fun z => (z.im : ℂ))

omit [DecidableEq ι] in
theorem CMSymplecticSiegel.CM.matrixConjugate_mul (M N : Matrix ι ι ℂ) :
    CMSymplecticSiegel.CM.matrixConjugate (M * N) = CMSymplecticSiegel.CM.matrixConjugate M * CMSymplecticSiegel.CM.matrixConjugate N := Matrix.map_mul

omit [Fintype ι] [DecidableEq ι] in
theorem CMSymplecticSiegel.CM.matrixConjugate_add (M N : Matrix ι ι ℂ) :
    CMSymplecticSiegel.CM.matrixConjugate (M + N) = CMSymplecticSiegel.CM.matrixConjugate M + CMSymplecticSiegel.CM.matrixConjugate N := by
  ext i j
  simp [CMSymplecticSiegel.CM.matrixConjugate]

theorem CMSymplecticSiegel.CM.matrixConjugate_inv (M : Matrix ι ι ℂ) :
    CMSymplecticSiegel.CM.matrixConjugate M⁻¹ = (CMSymplecticSiegel.CM.matrixConjugate M)⁻¹ := by
  change (M⁻¹ᴴ)ᵀ = (Mᴴᵀ)⁻¹
  rw [conjTranspose_nonsing_inv, transpose_nonsing_inv]

omit [Fintype ι] [DecidableEq ι] in
theorem CMSymplecticSiegel.CM.matrixConjugate_real (M : Matrix ι ι ℝ) :
    CMSymplecticSiegel.CM.matrixConjugate (M.map (algebraMap ℝ ℂ)) = M.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [CMSymplecticSiegel.CM.matrixConjugate]

theorem CMSymplecticSiegel.CM.matrixConjugate_det_isUnit (M : Matrix ι ι ℂ) (hM : IsUnit M.det) :
    IsUnit (CMSymplecticSiegel.CM.matrixConjugate M).det := by
  change IsUnit ((starRingEnd ℂ).mapMatrix M).det
  rw [← (starRingEnd ℂ).map_det]
  exact hM.map (starRingEnd ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem CMSymplecticSiegel.CM.matrix_sub_conjugate (M : Matrix ι ι ℂ) :
    M - CMSymplecticSiegel.CM.matrixConjugate M = (2 * Complex.I) • CMSymplecticSiegel.CM.matrixImaginary M := by
  ext i j
  apply Complex.ext <;> simp [CMSymplecticSiegel.CM.matrixConjugate, CMSymplecticSiegel.CM.matrixImaginary, Complex.mul_re, Complex.mul_im]
  ring

theorem CMSiegelMatrix.CM.SiegelMatrix.matrixImaginary_det_isUnit (Z : CMSiegelMatrix.CM.SiegelMatrix ι) :
    IsUnit (CMSymplecticSiegel.CM.matrixImaginary Z.matrix).det := by
  let Y : Matrix ι ι ℝ := fun i j => (Z.matrix i j).im
  change IsUnit ((algebraMap ℝ ℂ).mapMatrix Y).det
  rw [← (algebraMap ℝ ℂ).map_det]
  exact ((Matrix.isUnit_iff_isUnit_det Y).mp Z.imaginary_posDef.isUnit).map (algebraMap ℝ ℂ)

namespace CMSymplecticSiegel.CM.SymplecticBlocks

variable (g : SymplecticBlocks ι ℝ)

def complexify : SymplecticBlocks ι ℂ where
  A := g.A.map (algebraMap ℝ ℂ)
  B := g.B.map (algebraMap ℝ ℂ)
  C := g.C.map (algebraMap ℝ ℂ)
  D := g.D.map (algebraMap ℝ ℂ)
  symplectic := by
    simpa only [fromBlocks_map] using SymplecticGroup.map_mem g.symplectic (algebraMap ℝ ℂ)

theorem complexify_numerator_conjugate (Z : Matrix ι ι ℂ) :
    matrixConjugate (g.complexify.numerator Z) = g.complexify.numerator (matrixConjugate Z) := by
  change matrixConjugate (g.A.map (algebraMap ℝ ℂ) * Z + g.B.map (algebraMap ℝ ℂ)) = _
  rw [matrixConjugate_add, matrixConjugate_mul, matrixConjugate_real, matrixConjugate_real]
  rfl

theorem complexify_denominator_conjugate (Z : Matrix ι ι ℂ) :
    matrixConjugate (g.complexify.denominator Z) = g.complexify.denominator (matrixConjugate Z) := by
  change matrixConjugate (g.C.map (algebraMap ℝ ℂ) * Z + g.D.map (algebraMap ℝ ℂ)) = _
  rw [matrixConjugate_add, matrixConjugate_mul, matrixConjugate_real, matrixConjugate_real]
  rfl

theorem complexify_fractional_conjugate (Z : Matrix ι ι ℂ) :
    matrixConjugate (g.complexify.fractional Z) = g.complexify.fractional (matrixConjugate Z) := by
  rw [SymplecticBlocks.fractional, matrixConjugate_mul, matrixConjugate_inv,
    g.complexify_numerator_conjugate, g.complexify_denominator_conjugate]
  rfl

theorem complexify_fractional_imaginary (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm)
    (hJ : IsUnit (g.complexify.denominator Z).det) :
    (matrixConjugate (g.complexify.denominator Z))ᵀ *
        matrixImaginary (g.complexify.fractional Z) * g.complexify.denominator Z = matrixImaginary Z := by
  have hJc : IsUnit (g.complexify.denominator (matrixConjugate Z)).det := by
    rw [← g.complexify_denominator_conjugate]
    exact matrixConjugate_det_isUnit _ hJ
  have h := g.complexify.fractional_difference Z (matrixConjugate Z)
    (hZ.map (starRingEnd ℂ)) hJ hJc
  rw [← g.complexify_denominator_conjugate, ← g.complexify_fractional_conjugate,
    matrix_sub_conjugate, matrix_sub_conjugate, Matrix.mul_smul, Matrix.smul_mul] at h
  have h' := congrArg (fun M : Matrix ι ι ℂ => (2 * Complex.I)⁻¹ • M) h
  have hi : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul]
    using h'

theorem complexify_fractional_imaginary_inv (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm)
    (hJ : IsUnit (g.complexify.denominator Z).det) (hY : IsUnit (matrixImaginary Z).det) :
    (matrixImaginary (g.complexify.fractional Z))⁻¹ =
      g.complexify.denominator Z * (matrixImaginary Z)⁻¹ *
        (matrixConjugate (g.complexify.denominator Z))ᵀ := by
  have ht := g.complexify_fractional_imaginary Z hZ hJ
  have ht' : (matrixConjugate (g.complexify.denominator Z))ᵀ *
      matrixImaginary (g.complexify.fractional Z) = matrixImaginary Z * (g.complexify.denominator Z)⁻¹ := by
    calc
      _ = ((matrixConjugate (g.complexify.denominator Z))ᵀ *
          matrixImaginary (g.complexify.fractional Z) * g.complexify.denominator Z) *
          (g.complexify.denominator Z)⁻¹ := by rw [Matrix.mul_nonsing_inv_cancel_right _ _ hJ]
      _ = _ := by rw [ht]
  apply Matrix.inv_eq_left_inv
  calc
    _ = g.complexify.denominator Z * (matrixImaginary Z)⁻¹ *
        ((matrixConjugate (g.complexify.denominator Z))ᵀ * matrixImaginary (g.complexify.fractional Z)) := by
      simp only [Matrix.mul_assoc]
    _ = g.complexify.denominator Z * ((matrixImaginary Z)⁻¹ * matrixImaginary Z) *
        (g.complexify.denominator Z)⁻¹ := by rw [ht']; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [Matrix.nonsing_inv_mul _ hY, Matrix.mul_one, Matrix.mul_nonsing_inv _ hJ]

theorem complexify_denominator_sub_conjugate (Z : Matrix ι ι ℂ) :
    g.complexify.denominator Z - matrixConjugate (g.complexify.denominator Z) =
      (2 * Complex.I) • (g.complexify.C * matrixImaginary Z) := by
  rw [g.complexify_denominator_conjugate]
  calc
    _ = g.complexify.C * (Z - matrixConjugate Z) := by unfold SymplecticBlocks.denominator; noncomm_ring
    _ = _ := by rw [matrix_sub_conjugate, Matrix.mul_smul]

/-- Pulling back the inverse imaginary matrix by `J⁻ᵀ` changes its
quadratic form by exactly `-2i J⁻¹ C`, the correction in the manuscript. -/
theorem inverse_imaginary_pullback (Z : Matrix ι ι ℂ) (hZ : Z.IsSymm)
    (hJ : IsUnit (g.complexify.denominator Z).det) (hY : IsUnit (matrixImaginary Z).det) :
    (g.complexify.denominator Z)⁻¹ * (matrixImaginary (g.complexify.fractional Z))⁻¹ *
        (g.complexify.denominator Z)⁻¹ᵀ =
      (matrixImaginary Z)⁻¹ - (2 * Complex.I) •
        ((g.complexify.denominator Z)⁻¹ * g.complexify.C) := by
  have hdiff := congrArg Matrix.transpose (g.complexify_denominator_sub_conjugate Z)
  have hYsym : (matrixImaginary Z).IsSymm := hZ.map (fun z => (z.im : ℂ))
  rw [transpose_sub, transpose_smul, transpose_mul, hYsym.eq] at hdiff
  have hc : (matrixConjugate (g.complexify.denominator Z))ᵀ =
      (g.complexify.denominator Z)ᵀ - (2 * Complex.I) • (matrixImaginary Z * g.complexify.Cᵀ) := by
    calc
      _ = (g.complexify.denominator Z)ᵀ -
          ((g.complexify.denominator Z)ᵀ - (matrixConjugate (g.complexify.denominator Z))ᵀ) := by
        noncomm_ring
      _ = _ := by rw [hdiff]
  calc
    _ = (matrixImaginary Z)⁻¹ * (matrixConjugate (g.complexify.denominator Z))ᵀ *
        (g.complexify.denominator Z)⁻¹ᵀ := by
      rw [g.complexify_fractional_imaginary_inv Z hZ hJ hY]
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ, Matrix.one_mul]
    _ = (matrixImaginary Z)⁻¹ - (2 * Complex.I) •
        (g.complexify.Cᵀ * (g.complexify.denominator Z)⁻¹ᵀ) := by
      rw [hc, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
      simp only [transpose_nonsing_inv,
        Matrix.mul_nonsing_inv_cancel_right _ _ (Matrix.isUnit_det_transpose _ hJ),
        Matrix.nonsing_inv_mul_cancel_left _ _ hY]
    _ = _ := by rw [← transpose_mul, (g.complexify.correction_symmetric Z hZ hJ).eq]

end CMSymplecticSiegel.CM.SymplecticBlocks

end AlgebraicGeometry.ComplexMultiplication

namespace AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM
section

/-!
# The symplectic denominator is invertible on the Siegel domain

Positivity on real vectors extends to the real part of the Hermitian
quadratic expression on complex vectors. A vector in the kernel of
`CZ + D` would contradict this positivity through the inverse-free
symplectic cross identity. Thus denominator invertibility is proved
from the actual Siegel and real symplectic hypotheses.
-/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem complex_quadratic_realPart (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (algebraMap ℝ ℂ) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ (fun i => (v i).re)) +
      (fun i => (v i).im) ⬝ᵥ (Y *ᵥ (fun i => (v i).im)) := by
  simp [dotProduct, Matrix.mulVec, Complex.mul_re, Complex.mul_im,
    Finset.mul_sum, Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem complex_quadratic_realPart_pos (Y : Matrix ι ι ℝ) (hY : Y.PosDef)
    (v : ι → ℂ) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (Y.map (algebraMap ℝ ℂ) *ᵥ v)).re := by
  rw [complex_quadratic_realPart]
  have hr : 0 ≤ (fun i => (v i).re) ⬝ᵥ (Y *ᵥ (fun i => (v i).re)) := by
    simpa only [star_trivial] using hY.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have hi : 0 ≤ (fun i => (v i).im) ⬝ᵥ (Y *ᵥ (fun i => (v i).im)) := by
    simpa only [star_trivial] using hY.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
  by_cases hvr : (fun i => (v i).re) = 0
  · have hvi : (fun i => (v i).im) ≠ 0 := by
      intro hvi
      apply hv
      funext i
      apply Complex.ext
      · exact congrFun hvr i
      · exact congrFun hvi i
    have hip : 0 < (fun i => (v i).im) ⬝ᵥ (Y *ᵥ (fun i => (v i).im)) := by
      simpa only [star_trivial] using hY.dotProduct_mulVec_pos hvi
    exact add_pos_of_nonneg_of_pos hr hip
  · have hrp : 0 < (fun i => (v i).re) ⬝ᵥ (Y *ᵥ (fun i => (v i).re)) := by
      simpa only [star_trivial] using hY.dotProduct_mulVec_pos hvr
    exact add_pos_of_pos_of_nonneg hrp hi

omit [DecidableEq ι] in
theorem matrixConjugate_mulVec_star (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    matrixConjugate M *ᵥ star v = star (M *ᵥ v) := by
  funext i
  exact ((starRingEnd ℂ).map_mulVec M v i).symm

namespace SymplecticBlocks

variable (g : SymplecticBlocks ι ℝ) (Z : CMSiegelMatrix.CM.SiegelMatrix ι)

theorem denominator_kernel_eq_zero (v : ι → ℂ)
    (hv : g.complexify.denominator Z.matrix *ᵥ v = 0) : v = 0 := by
  by_contra hv0
  have hpos : 0 < (star v ⬝ᵥ (matrixImaginary Z.matrix *ᵥ v)).re :=
    complex_quadratic_realPart_pos _ Z.imaginary_posDef v hv0
  have hconj : matrixConjugate (g.complexify.denominator Z.matrix) *ᵥ star v = 0 := by
    rw [matrixConjugate_mulVec_star, hv, star_zero]
  have hcross := g.complexify.cross_difference Z.matrix (matrixConjugate Z.matrix)
    (Z.symmetric.map (starRingEnd ℂ))
  rw [← g.complexify_denominator_conjugate, ← g.complexify_numerator_conjugate,
    matrix_sub_conjugate] at hcross
  have h := congrArg (fun M : Matrix ι ι ℂ => star v ⬝ᵥ (M *ᵥ v)) hcross
  simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    dotProduct_transpose_mulVec, hconj, hv, Matrix.mulVec_zero, dotProduct_zero,
    sub_self, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h
  have hi : (2 * Complex.I : ℂ) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hzero : star v ⬝ᵥ (matrixImaginary Z.matrix *ᵥ v) = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left hi
  rw [hzero, Complex.zero_re] at hpos
  exact (lt_irrefl 0) hpos

/-- The actual denominator of every real symplectic substitution at a
positive Siegel matrix has nonzero determinant. -/
theorem denominator_det_isUnit : IsUnit (g.complexify.denominator Z.matrix).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w hvw
  apply sub_eq_zero.mp
  apply g.denominator_kernel_eq_zero Z
  rw [Matrix.mulVec_sub, hvw, sub_self]

/-- The inverse-imaginary-matrix correction now follows with no separate
invertibility assumptions for a genuine Siegel matrix. -/
theorem inverse_imaginary_pullback_siegel :
    (g.complexify.denominator Z.matrix)⁻¹ *
        (matrixImaginary (g.complexify.fractional Z.matrix))⁻¹ *
        (g.complexify.denominator Z.matrix)⁻¹ᵀ =
      (matrixImaginary Z.matrix)⁻¹ - (2 * Complex.I) •
        ((g.complexify.denominator Z.matrix)⁻¹ * g.complexify.C) :=
  g.inverse_imaginary_pullback Z.matrix Z.symmetric (g.denominator_det_isUnit Z)
    Z.matrixImaginary_det_isUnit

end SymplecticBlocks

end

/-!
# Real symplectic substitutions preserve the Siegel domain

The fractional matrix is symmetric and its imaginary part is positive
definite. This constructs the transformed Siegel matrix from the actual
real symplectic blocks, with no separate invertibility or positivity
premises on the result.
-/

open scoped _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem hermitian_matrix_pullback (K M : Matrix ι ι ℂ) (v : ι → ℂ) :
    star (K *ᵥ v) ⬝ᵥ (M *ᵥ (K *ᵥ v)) =
      star v ⬝ᵥ (((matrixConjugate K)ᵀ * M * K) *ᵥ v) := by
  symm
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_transpose_mulVec,
    matrixConjugate_mulVec_star, dotProduct_comm]

namespace SymplecticBlocks

variable (g : SymplecticBlocks ι ℝ) (Z : CMSiegelMatrix.CM.SiegelMatrix ι)

theorem fractional_imaginary_quadratic (v : ι → ℂ) :
    star (g.complexify.denominator Z.matrix *ᵥ v) ⬝ᵥ
        (matrixImaginary (g.complexify.fractional Z.matrix) *ᵥ
          (g.complexify.denominator Z.matrix *ᵥ v)) =
      star v ⬝ᵥ (matrixImaginary Z.matrix *ᵥ v) := by
  rw [hermitian_matrix_pullback,
    g.complexify_fractional_imaginary Z.matrix Z.symmetric (g.denominator_det_isUnit Z)]

theorem fractional_imaginary_complex_pos (v : ι → ℂ) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (matrixImaginary (g.complexify.fractional Z.matrix) *ᵥ v)).re := by
  let w := (g.complexify.denominator Z.matrix)⁻¹ *ᵥ v
  have hwv : g.complexify.denominator Z.matrix *ᵥ w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z), Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw
    apply hv
    rw [hw, Matrix.mulVec_zero] at hwv
    exact hwv.symm
  have hpos : 0 < (star w ⬝ᵥ (matrixImaginary Z.matrix *ᵥ w)).re :=
    complex_quadratic_realPart_pos _ Z.imaginary_posDef w hw
  have heq := g.fractional_imaginary_quadratic Z w
  rw [hwv] at heq
  rwa [heq]

theorem fractional_imaginary_posDef :
    Matrix.PosDef (fun i j => (g.complexify.fractional Z.matrix i j).im) := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.isHermitian_iff_isSymm.mpr
    exact (g.complexify.fractional_symmetric Z.matrix Z.symmetric
      (g.denominator_det_isUnit Z)).map Complex.im
  · intro v hv
    let vc : ι → ℂ := fun i => (v i : ℂ)
    have hvc : vc ≠ 0 := by
      intro h
      apply hv
      funext i
      have hi : (v i : ℂ) = 0 := congrFun h i
      exact_mod_cast hi
    have h := g.fractional_imaginary_complex_pos Z vc hvc
    let Y : Matrix ι ι ℝ := fun i j => (g.complexify.fractional Z.matrix i j).im
    change 0 < (star vc ⬝ᵥ (Y.map (algebraMap ℝ ℂ) *ᵥ vc)).re at h
    rw [complex_quadratic_realPart] at h
    simpa [vc] using h

/-- The transformed positive Siegel matrix. -/
def transformSiegel : CMSiegelMatrix.CM.SiegelMatrix ι where
  matrix := g.complexify.fractional Z.matrix
  symmetric := g.complexify.fractional_symmetric Z.matrix Z.symmetric (g.denominator_det_isUnit Z)
  imaginary_posDef := g.fractional_imaginary_posDef Z

theorem transformSiegel_matrix : (g.transformSiegel Z).matrix =
    (g.complexify.A * Z.matrix + g.complexify.B) *
      (g.complexify.C * Z.matrix + g.complexify.D)⁻¹ := rfl

end SymplecticBlocks

end AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM

end

end OAI
