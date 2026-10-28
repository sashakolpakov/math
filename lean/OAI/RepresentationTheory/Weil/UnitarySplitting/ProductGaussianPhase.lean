import OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianDiscriminant
import OAI.RepresentationTheory.Weil.UnitarySplitting.HermitianNormForms

/-! # Product Gaussian Phase -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ProductGaussianPhase.Construction

noncomputable section

/-! Identification of the sum of Cayley phases with its nondegenerate
Hermitian trace Gaussian, including the Weyl convention's factor of two. -/

open _root_.Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E)

omit [DecidableEq I] in
theorem sesquilinear_matrix_mul (A B : Matrix I I E) (x y : I → E) :
    DualPair.Construction.sesquilinear σ (A * B) x y = DualPair.Construction.sesquilinear σ A x (B *ᵥ y) := by
  simp only [DualPair.Construction.sesquilinear, Matrix.mulVec_mulVec]

omit [DecidableEq I] in
theorem sesquilinear_matrix_smul (a : E) (A : Matrix I I E) (x y : I → E) :
    DualPair.Construction.sesquilinear σ (a • A) x y = a * DualPair.Construction.sesquilinear σ A x y := by
  simp only [DualPair.Construction.sesquilinear, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

omit [DecidableEq I] in
theorem trace_sesquilinear_base_smul (a : F) (A : Matrix I I E) (x y : I → E) :
    Algebra.trace F E (DualPair.Construction.sesquilinear σ ((algebraMap F E a) • A) x y) =
      a * Algebra.trace F E (DualPair.Construction.sesquilinear σ A x y) := by
  rw [sesquilinear_matrix_smul, ← Algebra.smul_def, map_smul, smul_eq_mul]

variable [FiniteDimensional F E]

omit [DecidableEq I] [FiniteDimensional F E] in
theorem trace_sesquilinear_skew (hσ : Function.Involutive σ)
    (Q : Matrix I I E) (hQ : DualPair.Construction.adjointMatrix σ Q = -Q) (x y : I → E) :
    Algebra.trace F E (DualPair.Construction.sesquilinear σ Q y x) = -Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x y) := by
  rw [← Algebra.trace_eq_of_algEquiv σ (DualPair.Construction.sesquilinear σ Q y x),
    TracePairing.Construction.conjugate_sesquilinear σ hσ, hQ, TracePairing.Construction.sesquilinear_neg, map_neg]

omit [DecidableEq I] [FiniteDimensional F E] in
theorem trace_sesquilinear_skew_self [CharZero F] (hσ : Function.Involutive σ)
    (Q : Matrix I I E) (hQ : DualPair.Construction.adjointMatrix σ Q = -Q) (x : I → E) :
    Algebra.trace F E (DualPair.Construction.sesquilinear σ Q x x) = 0 := by
  have hh := trace_sesquilinear_skew σ hσ Q hQ x x
  linear_combination hh / 2

omit [FiniteDimensional F E] in
theorem unitaryProductGaussianMatrix_phase [CharZero F] (hσ : Function.Involutive σ)
    {d : ℕ} (Q : Matrix (Fin d) (Fin d) E) (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q)
    (g h : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (hh : h ∈ Generic.Construction.unitaryGenericDomain σ Q) (hgh : g * h ∈ Generic.Construction.unitaryGenericDomain σ Q)
    (v : Fin d → E) :
    HermitianNormForms.Construction.hermitianTraceQuadratic σ (GaussianDiscriminant.Construction.unitaryProductGaussianMatrix σ Q g h) v =
      Algebra.trace F E (DualPair.Construction.sesquilinear σ Q (((g.val : Matrix (Fin d) (Fin d) E) - 1)⁻¹ *ᵥ v) v) / 4 +
        Algebra.trace F E (DualPair.Construction.sesquilinear σ Q (((h.val : Matrix (Fin d) (Fin d) E) - 1)⁻¹ *ᵥ v) v) / 4 := by
  rw [HermitianNormForms.Construction.hermitianTraceQuadratic, GaussianDiscriminant.Construction.unitaryProductGaussianMatrix_expansion σ Q hQ hskew g h hg hh hgh,
    ← map_neg, trace_sesquilinear_base_smul, sesquilinear_matrix_mul]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    TracePairing.Construction.sesquilinear_add_right, TracePairing.Construction.sesquilinear_add_right, map_add, map_add,
    trace_sesquilinear_skew_self σ hσ Q hskew v,
    trace_sesquilinear_skew σ hσ Q hskew (((g.val : Matrix (Fin d) (Fin d) E) - 1)⁻¹ *ᵥ v) v,
    trace_sesquilinear_skew σ hσ Q hskew (((h.val : Matrix (Fin d) (Fin d) E) - 1)⁻¹ *ᵥ v) v]
  ring

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ProductGaussianPhase.Construction
