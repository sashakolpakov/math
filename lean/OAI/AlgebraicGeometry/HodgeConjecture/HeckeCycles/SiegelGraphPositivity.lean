import OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix
import Mathlib

/-! # Siegel Graph Positivity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SiegelGraphPositivity.CM

noncomputable section

/-! A genuine Siegel graph has positive imaginary alternating pairing
on every nonzero complex vector, by its real positive definite matrix. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM

variable {I : Type*} [Fintype I]

def pairing (p q : I → ℂ) : ℂ := ∑ i, (p i * star (q i) - q i * star (p i))

theorem cross_terms (Z : Matrix I I ℂ) (hZ : Z.IsSymm) (x : I → ℂ) :
    (∑ i, ∑ j, (Z i j).re * (x j).im * (x i).re) =
      ∑ i, ∑ j, (Z i j).re * (x j).re * (x i).im := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hZ.apply j i]
  ring

theorem imaginary (Z : Matrix I I ℂ) (hZ : Z.IsSymm) (x : I → ℂ) :
    (pairing (Z *ᵥ x) x).im =
      2 * ((fun i => (x i).re) ⬝ᵥ ((fun i j => (Z i j).im) *ᵥ (fun i => (x i).re)) +
        (fun i => (x i).im) ⬝ᵥ ((fun i j => (Z i j).im) *ᵥ (fun i => (x i).im))) := by
  have hc := cross_terms Z hZ x
  simp only [pairing, Complex.im_sum, Complex.sub_im, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Matrix.mulVec, dotProduct, Complex.re_sum,
    Complex.mul_re, Complex.im_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg]
  simp_rw [show ∀ i j, (x i).re * ((Z i j).re * (x j).im) =
      (Z i j).re * (x j).im * (x i).re by intros; ring,
    show ∀ i j, (x i).im * ((Z i j).re * (x j).re) =
      (Z i j).re * (x j).re * (x i).im by intros; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  simp only [mul_comm, mul_left_comm, mul_assoc] at hc ⊢
  rw [hc]
  ring_nf
  simp only [← Finset.sum_mul, add_comm]

theorem positive (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I) (x : I → ℂ) (hx : x ≠ 0) :
    0 < (pairing (Z.matrix *ᵥ x) x).im := by
  rw [imaginary Z.matrix Z.symmetric]
  have hr : 0 ≤ (fun i => (x i).re) ⬝ᵥ
      ((fun i j => (Z.matrix i j).im) *ᵥ (fun i => (x i).re)) := by
    simpa only [star_trivial] using Z.imaginary_posDef.posSemidef.dotProduct_mulVec_nonneg
      (fun i => (x i).re)
  have hi : 0 ≤ (fun i => (x i).im) ⬝ᵥ
      ((fun i j => (Z.matrix i j).im) *ᵥ (fun i => (x i).im)) := by
    simpa only [star_trivial] using Z.imaginary_posDef.posSemidef.dotProduct_mulVec_nonneg
      (fun i => (x i).im)
  by_cases hre : (fun i => (x i).re) = 0
  · have him : (fun i => (x i).im) ≠ 0 := by
      intro him
      apply hx
      funext i
      exact Complex.ext (congrFun hre i) (congrFun him i)
    have hp := Z.imaginary_posDef.dotProduct_mulVec_pos him
    simp only [star_trivial] at hp
    linarith
  · have hp := Z.imaginary_posDef.dotProduct_mulVec_pos hre
    simp only [star_trivial] at hp
    linarith

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SiegelGraphPositivity.CM
