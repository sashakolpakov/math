import OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame

/-! # Positive Graph -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization

noncomputable section

/-! Constructing a Siegel matrix from a positive isotropic period frame. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def standardFramePairing (p q : ι → ℂ) : ℂ :=
  ∑ i, (p i * star (q i) - q i * star (p i))

theorem positive_frame_lower_det
    (P Q : Matrix ι ι ℂ)
    (hpositive : ∀ v : ι → ℂ, v ≠ 0 →
      0 < (standardFramePairing (P *ᵥ v) (Q *ᵥ v)).im) :
    Q.det ≠ 0 := by
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det Q).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  by_contra hne
  have hv : Q *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hp := hpositive (x - y) (sub_ne_zero.mpr hne)
  simp [hv, standardFramePairing] at hp

theorem isotropic_frame_graph_symmetric
    (P Q : Matrix ι ι ℂ) (hQ : Q.det ≠ 0)
    (hisotropic : P.transpose * Q = Q.transpose * P) :
    (P * Q⁻¹).IsSymm := by
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have ht : Q⁻¹ᵀ * Q.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hQi
  change (P * Q⁻¹).transpose = P * Q⁻¹
  calc
    _ = Q⁻¹ᵀ * P.transpose := Matrix.transpose_mul _ _
    _ = (Q⁻¹ᵀ * P.transpose) * (Q * Q⁻¹) := by rw [hQi, Matrix.mul_one]
    _ = Q⁻¹ᵀ * (P.transpose * Q) * Q⁻¹ := by simp only [Matrix.mul_assoc]
    _ = Q⁻¹ᵀ * (Q.transpose * P) * Q⁻¹ := by rw [hisotropic]
    _ = (Q⁻¹ᵀ * Q.transpose) * P * Q⁻¹ := by simp only [Matrix.mul_assoc]
    _ = P * Q⁻¹ := by rw [ht, Matrix.one_mul]

omit [DecidableEq ι] in
theorem graph_pairing_im (Z : Matrix ι ι ℂ) (w : ι → ℝ) :
    (standardFramePairing (Z *ᵥ (fun i => (w i : ℂ))) (fun i => (w i : ℂ))).im =
      2 * (w ⬝ᵥ ((fun i j => (Z i j).im) *ᵥ w)) := by
  simp only [standardFramePairing, Complex.im_sum, Complex.sub_im, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, zero_add, add_zero, neg_zero]
  simp only [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The upper-half-space point is constructed from the frame, rather than
postulated independently of the positive Lagrangian. -/
def siegelOfPositiveFrame (P Q : Matrix ι ι ℂ)
    (hisotropic : P.transpose * Q = Q.transpose * P)
    (hpositive : ∀ v : ι → ℂ, v ≠ 0 →
      0 < (standardFramePairing (P *ᵥ v) (Q *ᵥ v)).im) : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι where
  matrix := P * Q⁻¹
  symmetric := isotropic_frame_graph_symmetric P Q (positive_frame_lower_det P Q hpositive) hisotropic
  imaginary_posDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.isHermitian_iff_isSymm.mpr
      exact (isotropic_frame_graph_symmetric P Q (positive_frame_lower_det P Q hpositive) hisotropic).map Complex.im
    · intro w hw
      let wc : ι → ℂ := fun i => (w i : ℂ)
      let v := Q⁻¹ *ᵥ wc
      have hQ := positive_frame_lower_det P Q hpositive
      have hQv : Q *ᵥ v = wc := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ),
          Matrix.one_mulVec]
      have hv : v ≠ 0 := by
        intro hv
        have he : wc = 0 := by rw [← hQv, hv, Matrix.mulVec_zero]
        apply hw
        funext i
        have hi : (w i : ℂ) = 0 := congrFun he i
        exact_mod_cast hi
      have hp := hpositive v hv
      have hPv : P *ᵥ v = (P * Q⁻¹) *ᵥ wc := Matrix.mulVec_mulVec _ _ _
      rw [hQv, hPv, graph_pairing_im] at hp
      simp only [star_trivial] at *
      linarith

theorem siegelOfPositiveFrame_columns (P Q : Matrix ι ι ℂ)
    (hisotropic : P.transpose * Q = Q.transpose * P)
    (hpositive : ∀ v : ι → ℂ, v ≠ 0 →
      0 < (standardFramePairing (P *ᵥ v) (Q *ᵥ v)).im) :
    (siegelOfPositiveFrame P Q hisotropic hpositive).matrix * Q = P := by
  change P * Q⁻¹ * Q = P
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (positive_frame_lower_det P Q hpositive)), Matrix.mul_one]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.PositiveGraph.Realization
