import OAI.RepresentationTheory.Hecke.RadialDilation.Complexification

/-! # Rational Coordinates -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization

noncomputable section

section

/-! Rational coordinate matrices and their actual complex embedding realization. -/

open scoped Classical TensorProduct _root_.Matrix

section

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
variable {Place κ : Type*} [Fintype κ] [DecidableEq κ]

def rationalCoordinates
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) :
    Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (κ → ℂ) :=
  (Complexification.Realization.pairedComplexification E σ hσ).symm.trans
    ((e.baseChange ℚ ℂ _ _).trans (TensorProduct.piScalarRight ℚ ℂ ℂ κ))

theorem rationalCoordinates_tmul
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) (z : ℂ) (x : Fin 3 → E) :
    rationalCoordinates E σ hσ e (Complexification.Realization.pairedComplexification E σ hσ (z ⊗ₜ[ℚ] x)) =
      z • (fun i => (e x i : ℂ)) := by
  simp [rationalCoordinates, Algebra.smul_def, mul_comm]
  rfl

def rationalScalarMatrix (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) (r : E) : Matrix κ κ ℚ :=
  LinearMap.toMatrix' ((e.toLinearMap.comp (Complexification.Realization.rationalScalarEnd E r)).comp e.symm.toLinearMap)

omit [NumberField E] in
theorem rationalScalarMatrix_apply (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ))
    (r : E) (x : Fin 3 → E) :
    rationalScalarMatrix E e r *ᵥ e x = e (Complexification.Realization.rationalScalarEnd E r x) := by
  rw [rationalScalarMatrix, LinearMap.toMatrix'_mulVec]
  simp

omit [DecidableEq κ] in
theorem rational_matrix_complex_mulVec (M : Matrix κ κ ℚ) (v : κ → ℚ) :
    M.map (algebraMap ℚ ℂ) *ᵥ (fun i => (v i : ℂ)) =
      fun i => ((M *ᵥ v) i : ℂ) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

end

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
variable {Place κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Choosing any rational basis gives a rational matrix for multiplication by r;
its complex realization is precisely the paired scalar computed on period frames. -/
theorem rational_matrix_realizes_scalar
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (κ → ℚ)) (u : Geometry.ComplexBall.PrescribedSignsB.Ambient Place) :
    rationalCoordinates E σ hσ e (Complexification.Realization.pairedScalarEnd (fun τ => σ τ (r : E)) u) =
      (rationalScalarMatrix E e (r : E)).map (algebraMap ℚ ℂ) *ᵥ
        rationalCoordinates E σ hσ e u := by
  obtain ⟨x, rfl⟩ := (Complexification.Realization.pairedComplexification E σ hσ).surjective u
  rw [← Complexification.Realization.scalar_complexification_identification E r hr σ hσ]
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]
  | tmul z x =>
      rw [LinearMap.baseChange_tmul, rationalCoordinates_tmul, rationalCoordinates_tmul,
        Matrix.mulVec_smul, rational_matrix_complex_mulVec, rationalScalarMatrix_apply]

end

/-! Positive powers retain the concrete rational scalar matrix and norm-one relation. -/

open scoped Classical _root_.Matrix

theorem rationalScalarMatrix_pow
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E) (N : ℕ) :
    rationalScalarMatrix E e r ^ N = rationalScalarMatrix E e (r ^ N) := by
  have hp (k : ℕ) (x : Fin 3 → E) :
      rationalScalarMatrix E e r ^ k *ᵥ e x = e (fun i => r ^ k * x i) := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, rationalScalarMatrix_apply]
        congr 1
        funext i
        change r * (r ^ k * x i) = r ^ (k + 1) * x i
        rw [pow_succ', mul_assoc]
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [hp, rationalScalarMatrix_apply]
  rfl

theorem cm_norm_one_power
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ) (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1) (N : ℕ) :
    (r ^ N : Eˣ).val * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r ^ N : Eˣ).val = 1 := by
  rw [Units.val_pow_eq_pow_val, map_pow, ← mul_pow, hr, one_pow]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RationalCoordinates.Realization
