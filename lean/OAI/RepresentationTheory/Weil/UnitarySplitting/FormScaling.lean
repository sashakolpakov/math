import OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant

/-! # Form Scaling -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling.Construction

noncomputable section

/-! Scalar changes of a unitary form and diagonalization of a
skew-Hermitian form by a fixed antifixed scalar. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E) (Q : Matrix I I E)

def unitaryScaleForm (z : E) : DualPair.Construction.unitaryGroup σ Q →* DualPair.Construction.unitaryGroup σ (z • Q) where
  toFun g := ⟨g.val, by
    change DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * (z • Q) * (g.val : Matrix I I E) = z • Q
    rw [mul_smul_comm, smul_mul_assoc, g.property]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem unitaryScaleForm_matrix (z : E) (g : DualPair.Construction.unitaryGroup σ Q) :
    ((unitaryScaleForm σ Q z g).val : Matrix I I E) = (g.val : Matrix I I E) := rfl

theorem unitaryScaleForm_generic (z : E) (g : DualPair.Construction.unitaryGroup σ Q) :
    unitaryScaleForm σ Q z g ∈ Generic.Construction.unitaryGenericDomain σ (z • Q) ↔ g ∈ Generic.Construction.unitaryGenericDomain σ Q := Iff.rfl

theorem unitaryScaleForm_surjective (z : E) (hz : z ≠ 0) :
    Function.Surjective (unitaryScaleForm σ Q z) := by
  intro g
  have hg : DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * Q * (g.val : Matrix I I E) = Q := by
    apply (smul_right_injective (Matrix I I E) hz)
    have hh := g.property
    change DualPair.Construction.adjointMatrix σ (g.val : Matrix I I E) * (z • Q) * (g.val : Matrix I I E) = z • Q at hh
    rwa [mul_smul_comm, smul_mul_assoc] at hh
  exact ⟨⟨g.val, hg⟩, rfl⟩

omit Q [Fintype I] [DecidableEq I] in
theorem antifixed_hermitian_scale (z : E) (hz : σ z = -z)
    (A : Matrix I I E) (hA : DualPair.Construction.adjointMatrix σ A = A) :
    DualPair.Construction.adjointMatrix σ (z • A) = -(z • A) := by
  rw [Generic.Construction.adjointMatrix_smul, hz, hA, neg_smul]

omit Q [Fintype I] [DecidableEq I] in
theorem antifixed_skew_scale (z : E) (hz : σ z = -z)
    (A : Matrix I I E) (hA : DualPair.Construction.adjointMatrix σ A = -A) :
    DualPair.Construction.adjointMatrix σ (z⁻¹ • A) = z⁻¹ • A := by
  rw [Generic.Construction.adjointMatrix_smul, map_inv₀, hz, inv_neg, hA, neg_smul, smul_neg, neg_neg]

theorem hermitian_diagonal_units [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0) :
    ∃ u : (Matrix (Fin n) (Fin n) E)ˣ, ∃ a : Fin n → Fˣ,
      DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E) = TensorUnitary.Construction.multiplicityForm a := by
  obtain ⟨u, a, ha, hdiag⟩ := HermitianGaussianDiscriminant.Construction.hermitian_matrix_diagonal σ hQuadratic hne A hA hdet
  exact ⟨u, fun i => Units.mk0 (a i) (ha i), hdiag⟩

theorem skewHermitian_diagonal_units [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)
    {n : ℕ} (A : Matrix (Fin n) (Fin n) E) (hA : DualPair.Construction.adjointMatrix σ A = -A) (hdet : A.det ≠ 0)
    (z : E) (hz0 : z ≠ 0) (hz : σ z = -z) :
    ∃ u : (Matrix (Fin n) (Fin n) E)ˣ, ∃ a : Fin n → Fˣ,
      DualPair.Construction.adjointMatrix σ (u : Matrix (Fin n) (Fin n) E) * A * (u : Matrix (Fin n) (Fin n) E) = z • TensorUnitary.Construction.multiplicityForm a := by
  have hscaled : (z⁻¹ • A).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hz0)) hdet
  obtain ⟨u, a, hdiag⟩ := hermitian_diagonal_units σ hQuadratic hne (z⁻¹ • A)
    (antifixed_skew_scale σ z hz A hA) hscaled
  have hh := congrArg (fun M : Matrix (Fin n) (Fin n) E => z • M) hdiag
  rw [mul_smul_comm, smul_mul_assoc, smul_smul, mul_inv_cancel₀ hz0, one_smul] at hh
  exact ⟨u, a, hh⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.FormScaling.Construction
