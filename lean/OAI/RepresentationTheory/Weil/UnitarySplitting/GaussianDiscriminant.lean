import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant

/-! # Gaussian Discriminant -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianDiscriminant.Construction

noncomputable section

section

/-! The Hermitian matrix representing the Gaussian in a generic unitary
product, expressed as a congruence of the inverse product form. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E)

omit [Fintype I] [DecidableEq I] in
theorem adjointMatrix_base_smul (a : F) (A : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ ((algebraMap F E a) • A) = (algebraMap F E a) • DualPair.Construction.adjointMatrix σ A := by
  ext i j
  change σ (algebraMap F E a * A j i) = algebraMap F E a * σ (A j i)
  rw [map_mul, σ.commutes]

def unitaryProductGaussianMatrix (Q : Matrix I I E) (g h : DualPair.Construction.unitaryGroup σ Q) : Matrix I I E :=
  (algebraMap F E (1 / 2)) •
    (DualPair.Construction.adjointMatrix σ Q * (CayleyProduct.Construction.unitaryProductForm σ Q g h)⁻¹ * Q)

variable [CharZero F]
variable (Q : Matrix I I E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
variable (g h : DualPair.Construction.unitaryGroup σ Q)
variable (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q)
variable (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q)

include hQ hskew hg hh hgh in
theorem unitaryProductGaussianMatrix_hermitian (hσ : Function.Involutive σ) :
    DualPair.Construction.adjointMatrix σ (unitaryProductGaussianMatrix σ Q g h) = unitaryProductGaussianMatrix σ Q g h := by
  have hS := CayleyProduct.Construction.unitaryProductForm_hermitian σ hσ Q hQ hskew g h hg hh hgh
  have hSn := CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh
  rw [unitaryProductGaussianMatrix, adjointMatrix_base_smul, DualPair.Construction.adjointMatrix_mul, DualPair.Construction.adjointMatrix_mul,
    TracePairing.Construction.adjointMatrix_involutive σ hσ, CayleyProduct.Construction.adjointMatrix_nonsing_inv σ _ hSn, hS, mul_assoc]

include hQ hg hh hgh in
theorem unitaryProductGaussianMatrix_nondegenerate :
    (unitaryProductGaussianMatrix σ Q g h).det ≠ 0 := by
  have ha : algebraMap F E (1 / 2 : F) ≠ 0 :=
    (map_ne_zero (algebraMap F E)).mpr (one_div_ne_zero (two_ne_zero : (2 : F) ≠ 0))
  rw [unitaryProductGaussianMatrix, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
    TracePairing.Construction.adjointMatrix_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact mul_ne_zero (pow_ne_zero _ ha)
    (mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr hQ)
      (inv_ne_zero (CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh))) hQ)

include hQ hskew hg hh hgh in
omit [CharZero F] in
theorem unitaryProductGaussianMatrix_expansion :
    unitaryProductGaussianMatrix σ Q g h =
      -(algebraMap F E (1 / 2)) •
        (Q * (1 + ((g.val : Matrix I I E) - 1)⁻¹ + ((h.val : Matrix I I E) - 1)⁻¹)) := by
  rw [unitaryProductGaussianMatrix, hskew, CayleyProduct.Construction.unitaryProductForm_inverse σ Q hQ g h hg hh hgh]
  rw [mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hQ), mul_one,
    neg_mul, smul_neg, neg_smul]

end

/-! The determinant character of the product Gaussian differs from that
of the unitary product form by one fixed half-scalar per dimension. -/

open _root_.Matrix

theorem quadraticCharacter_inv
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [FiniteDimensional F E]
    (hQuadratic : Module.finrank F E = 2) (ω : Fˣ →ₜ* Circle)
    (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω) (b : Fˣ) : (ω b)⁻¹ = ω b := by
  have hh := congrArg (fun z : Circle => z * (ω b)⁻¹) (Characters.Construction.quadraticCharacter_square hQuadratic ω hω b)
  simp only [pow_two, mul_assoc, mul_inv_cancel, mul_one, one_mul] at hh
  exact hh.symm

theorem unitaryProductGaussianMatrix_discriminant
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    {d : ℕ} (Q : Matrix (Fin d) (Fin d) E) (hQ : Q.det ≠ 0)
    (g h : DualPair.Construction.unitaryGroup σ Q) (b : Fˣ)
    (hb : algebraMap F E (b : F) = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det) :
    ∃ a : Fˣ, algebraMap F E (a : F) = (unitaryProductGaussianMatrix σ Q g h).det ∧
      ω a = ω (Units.mk0 (1 / 2 : F) (one_div_ne_zero two_ne_zero)) ^ d * ω b := by
  let t : Eˣ := TensorUnitary.Construction.matrixDetUnit (Q.nonsingInvUnit (isUnit_iff_ne_zero.mpr hQ))
  let s : Fˣ := Units.mk0 (1 / 2 : F) (one_div_ne_zero two_ne_zero)
  let a := s ^ d * Units.map (Algebra.norm F) t * b⁻¹
  refine ⟨a, ?_, ?_⟩
  · dsimp only [a]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_inv_eq_inv_val]
    change algebraMap F E ((1 / 2 : F) ^ d * Algebra.norm F (t : E) * (b : F)⁻¹) = _
    rw [map_mul, map_mul, map_pow, map_inv₀, hb, QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne,
      unitaryProductGaussianMatrix, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul,
      TracePairing.Construction.adjointMatrix_det, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, Fintype.card_fin]
    change (algebraMap F E (1 / 2)) ^ d * (Q.det * σ Q.det) *
      (CayleyProduct.Construction.unitaryProductForm σ Q g h).det⁻¹ =
        (algebraMap F E (1 / 2)) ^ d * (σ Q.det * (CayleyProduct.Construction.unitaryProductForm σ Q g h).det⁻¹ * Q.det)
    ring
  · have ht : ω (Units.map (Algebra.norm F) t) = 1 := (hω _).mpr ⟨t, rfl⟩
    change ω (s ^ d * Units.map (Algebra.norm F) t * b⁻¹) = ω s ^ d * ω b
    rw [map_mul, map_mul, map_pow, ht, mul_one, map_inv,
      quadraticCharacter_inv hQuadratic ω hω]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianDiscriminant.Construction
