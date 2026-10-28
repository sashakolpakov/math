import OAI.RepresentationTheory.Weil.UnitarySplitting.Generic

/-! # Cayley Product -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyProduct.Construction

noncomputable section

/-! The nonsingular Hermitian form in the generic unitary product formula. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E)

theorem adjointMatrix_nonsing_inv (A : Matrix I I E) (hA : A.det ≠ 0) :
    DualPair.Construction.adjointMatrix σ A⁻¹ = (DualPair.Construction.adjointMatrix σ A)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← DualPair.Construction.adjointMatrix_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA), DualPair.Construction.adjointMatrix_one]

theorem adjointMatrix_skew_inv (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (hskew : DualPair.Construction.adjointMatrix σ Q = -Q) : DualPair.Construction.adjointMatrix σ Q⁻¹ = -Q⁻¹ := by
  rw [adjointMatrix_nonsing_inv σ Q hQ, hskew]
  exact Matrix.inv_eq_left_inv (by
    rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ)])

theorem unitaryCayleyForm_expansion (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q)
    (hg : ((g.val : Matrix I I E) - 1).det ≠ 0) :
    TracePairing.Construction.unitaryCayleyForm σ Q g = Q + Q * ((g.val : Matrix I I E) - 1)⁻¹ +
      Q * ((g.val : Matrix I I E) - 1)⁻¹ := by
  unfold TracePairing.Construction.unitaryCayleyForm
  calc
    _ = Q * ((g.val : Matrix I I E) - 1) * ((g.val : Matrix I I E) - 1)⁻¹ +
        Q * ((g.val : Matrix I I E) - 1)⁻¹ + Q * ((g.val : Matrix I I E) - 1)⁻¹ := by
          noncomm_ring
    _ = _ := by rw [mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hg), mul_one]

theorem matrix_difference_inverse_product (A B : Matrix I I E)
    (hA : (A - 1).det ≠ 0) (hB : (B - 1).det ≠ 0) :
    (A - 1)⁻¹ * (A * B - 1) * (B - 1)⁻¹ = 1 + (A - 1)⁻¹ + (B - 1)⁻¹ := by
  have hab : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [hab]
  calc
    _ = (A - 1)⁻¹ * (A - 1) * ((B - 1) * (B - 1)⁻¹) +
        (A - 1)⁻¹ * (A - 1) * (B - 1)⁻¹ + (A - 1)⁻¹ * ((B - 1) * (B - 1)⁻¹) := by
          noncomm_ring
    _ = _ := by
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB)]
      simp only [one_mul, mul_one]
      abel

def unitaryProductForm (Q : Matrix I I E) (g h : DualPair.Construction.unitaryGroup σ Q) : Matrix I I E :=
  Q * ((h.val : Matrix I I E) - 1) * (((g * h).val : Matrix I I E) - 1)⁻¹ *
    ((g.val : Matrix I I E) - 1)

theorem unitaryProductForm_det (Q : Matrix I I E) (g h : DualPair.Construction.unitaryGroup σ Q) :
    (unitaryProductForm σ Q g h).det =
      Q.det * ((h.val : Matrix I I E) - 1).det *
        (((g * h).val : Matrix I I E) - 1).det⁻¹ * ((g.val : Matrix I I E) - 1).det := by
  simp only [unitaryProductForm, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]

theorem unitaryProductForm_nondegenerate (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (g h : DualPair.Construction.unitaryGroup σ Q)
    (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) : (unitaryProductForm σ Q g h).det ≠ 0 := by
  rw [unitaryProductForm_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hQ hh) (inv_ne_zero hgh)) hg

theorem unitaryProductForm_inverse (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (g h : DualPair.Construction.unitaryGroup σ Q)
    (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    (unitaryProductForm σ Q g h)⁻¹ =
      (1 + ((g.val : Matrix I I E) - 1)⁻¹ + ((h.val : Matrix I I E) - 1)⁻¹) * Q⁻¹ := by
  have hQg : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  have hga : IsUnit ((g.val : Matrix I I E) - 1).det := isUnit_iff_ne_zero.mpr hg
  have hha : IsUnit ((h.val : Matrix I I E) - 1).det := isUnit_iff_ne_zero.mpr hh
  have hgha : IsUnit (((g * h).val : Matrix I I E) - 1).det := isUnit_iff_ne_zero.mpr hgh
  have heq := matrix_difference_inverse_product (g.val : Matrix I I E) (h.val : Matrix I I E) hg hh
  rw [← heq]
  apply Matrix.inv_eq_right_inv
  change Q * ((h.val : Matrix I I E) - 1) * (((g * h).val : Matrix I I E) - 1)⁻¹ *
    ((g.val : Matrix I I E) - 1) *
      (((g.val : Matrix I I E) - 1)⁻¹ * (((g * h).val : Matrix I I E) - 1) *
        ((h.val : Matrix I I E) - 1)⁻¹ * Q⁻¹) = 1
  simp only [mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hga,
    Matrix.nonsing_inv_mul_cancel_left _ _ hgha,
    Matrix.mul_nonsing_inv_cancel_left _ _ hha,
    Matrix.mul_nonsing_inv _ hQg]

theorem unitaryProductForm_twice_inverse (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (g h : DualPair.Construction.unitaryGroup σ Q)
    (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    Q⁻¹ * (TracePairing.Construction.unitaryCayleyForm σ Q g + TracePairing.Construction.unitaryCayleyForm σ Q h) * Q⁻¹ =
      (unitaryProductForm σ Q g h)⁻¹ + (unitaryProductForm σ Q g h)⁻¹ := by
  rw [unitaryProductForm_inverse σ Q hQ g h hg hh hgh,
    unitaryCayleyForm_expansion σ Q g hg, unitaryCayleyForm_expansion σ Q h hh]
  simp only [mul_add, add_mul, one_mul,
    Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.mpr hQ),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ)]
  abel

theorem unitaryProductForm_hermitian [CharZero F]
    (hσ : Function.Involutive σ) (Q : Matrix I I E) (hQ : Q.det ≠ 0)
    (hskew : DualPair.Construction.adjointMatrix σ Q = -Q) (g h : DualPair.Construction.unitaryGroup σ Q)
    (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q) :
    DualPair.Construction.adjointMatrix σ (unitaryProductForm σ Q g h) = unitaryProductForm σ Q g h := by
  let : CharZero E := Algebra.charZero_of_charZero F E
  have hsum : DualPair.Construction.adjointMatrix σ (Q⁻¹ * (TracePairing.Construction.unitaryCayleyForm σ Q g + TracePairing.Construction.unitaryCayleyForm σ Q h) * Q⁻¹) =
      Q⁻¹ * (TracePairing.Construction.unitaryCayleyForm σ Q g + TracePairing.Construction.unitaryCayleyForm σ Q h) * Q⁻¹ := by
    rw [DualPair.Construction.adjointMatrix_mul, DualPair.Construction.adjointMatrix_mul, adjointMatrix_skew_inv σ Q hQ hskew,
      TracePairing.Construction.adjointMatrix_add, TracePairing.Construction.unitaryCayleyForm_hermitian σ hσ Q hskew g hg,
      TracePairing.Construction.unitaryCayleyForm_hermitian σ hσ Q hskew h hh]
    noncomm_ring
  rw [unitaryProductForm_twice_inverse σ Q hQ g h hg hh hgh, TracePairing.Construction.adjointMatrix_add] at hsum
  have hinv : DualPair.Construction.adjointMatrix σ (unitaryProductForm σ Q g h)⁻¹ =
      (unitaryProductForm σ Q g h)⁻¹ := by
    ext i j
    have he := congrFun (congrFun hsum i) j
    change DualPair.Construction.adjointMatrix σ (unitaryProductForm σ Q g h)⁻¹ i j +
        DualPair.Construction.adjointMatrix σ (unitaryProductForm σ Q g h)⁻¹ i j =
      (unitaryProductForm σ Q g h)⁻¹ i j + (unitaryProductForm σ Q g h)⁻¹ i j at he
    linear_combination (1 / 2 : E) * he
  have hdet := unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh
  rw [adjointMatrix_nonsing_inv σ _ hdet] at hinv
  exact (Matrix.inv_inj hinv.symm (isUnit_iff_ne_zero.mpr hdet)).symm

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyProduct.Construction
