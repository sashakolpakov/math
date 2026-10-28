import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianGaussianDiscriminant

/-! # Hermitian Norm Forms -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianNormForms.Construction

noncomputable section

/-! The diagonal Hermitian form is an explicit sum of one-dimensional
quadratic norms. This is the algebraic reduction for the Gaussian identity. -/

open _root_.Matrix
open scoped BigOperators

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] [CharZero F]
variable (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
variable (hne : ∃ z : E, σ z ≠ z) {n : ℕ}

include hQuadratic hne in
theorem sesquilinear_diagonal_norm (a : Fin n → F) (z : Fin n → E) :
    DualPair.Construction.sesquilinear σ (Matrix.diagonal (fun i => algebraMap F E (a i))) z z =
      algebraMap F E (∑ i, a i * Algebra.norm F (z i)) := by
  simp only [DualPair.Construction.sesquilinear, Matrix.mulVec_diagonal, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [QuadraticNorm.Construction.quadratic_norm_formula hQuadratic σ hne]
  ring

include hQuadratic hne in
theorem hermitian_norm_coordinates (A : Matrix (Fin n) (Fin n) E)
    (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0) :
    ∃ u : (Matrix (Fin n) (Fin n) E)ˣ, ∃ a : Fin n → F,
      (∀ i, a i ≠ 0) ∧ ∀ z : Fin n → E,
        DualPair.Construction.sesquilinear σ A ((u : Matrix (Fin n) (Fin n) E) *ᵥ z)
          ((u : Matrix (Fin n) (Fin n) E) *ᵥ z) =
            algebraMap F E (∑ i, a i * Algebra.norm F (z i)) := by
  obtain ⟨u, a, ha, hdiag⟩ := HermitianGaussianDiscriminant.Construction.hermitian_matrix_diagonal σ hQuadratic hne A hA hdet
  refine ⟨u, a, ha, fun z => ?_⟩
  rw [DualPair.Construction.sesquilinear_change, hdiag]
  exact sesquilinear_diagonal_norm hQuadratic σ hne a z

def hermitianTraceQuadratic (A : Matrix (Fin n) (Fin n) E) (z : Fin n → E) : F :=
  Algebra.trace F E (DualPair.Construction.sesquilinear σ A z z) / 2

include hQuadratic hne in
theorem hermitianTraceQuadratic_norm_coordinates (A : Matrix (Fin n) (Fin n) E)
    (hA : DualPair.Construction.adjointMatrix σ A = A) (hdet : A.det ≠ 0) :
    ∃ u : (Matrix (Fin n) (Fin n) E)ˣ, ∃ a : Fin n → F,
      (∀ i, a i ≠ 0) ∧ ∀ z : Fin n → E,
        hermitianTraceQuadratic σ A ((u : Matrix (Fin n) (Fin n) E) *ᵥ z) =
          ∑ i, a i * Algebra.norm F (z i) := by
  obtain ⟨u, a, ha, hform⟩ := hermitian_norm_coordinates hQuadratic σ hne A hA hdet
  refine ⟨u, a, ha, fun z => ?_⟩
  unfold hermitianTraceQuadratic
  rw [hform, Algebra.trace_algebraMap, hQuadratic]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianNormForms.Construction
