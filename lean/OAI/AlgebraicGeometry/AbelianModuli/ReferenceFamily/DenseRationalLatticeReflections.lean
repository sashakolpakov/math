import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticReflectionApproximation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMIntegralDenseCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeReflectionCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixFormScaling

/-! # Dense Rational Lattice Reflections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DenseRationalLatticeReflections

noncomputable section

/-! Rational Hermitian reflection products satisfying the original
lattice congruences approximate the actual complex negative-vector
orbits. The given form and fixed vector may have arbitrary number-field
coefficients: integral clearing and reflection equality are proved here.
-/

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem exists_rational_lattice_reflections_in_orbit_neighborhood
    (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (w : Fin 3 → E)
    (hw : MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H w w ≠ 0)
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (N : ℕ) (hN : 0 < N) (x y : Fin 3 → ℂ)
    (hx : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) x x = -1)
    (hy : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) y y = -1)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U)
    (hyU : ∀ u : ℂ, ‖u‖ = 1 → u • y ∈ U) :
    ∃ g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      ((LinearMap.toMatrix' g.toLinearMap).map μ).mulVec x ∈ U ∧
      (∀ a d, MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H
        (g a) (g d) =
          MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H a d) ∧
      LinearMap.det g.toLinearMap = 1 ∧
      LatticeReflectionCongruence.ClearedPrincipalLatticeCongruence Λ N g := by
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  let B := MatrixReflectionEmbedding.matrixReflectionForm σ H
  have hσ : Function.Involutive σ := NumberField.IsCMField.complexConj_apply_apply E
  have hμ : ∀ a, μ (σ a) = star (μ a) :=
    NumberField.IsCMField.complexEmbedding_complexConj E μ
  obtain ⟨d, hd, H₀, w₀, hH₀, hw₀⟩ := Integral.CoefficientClearing.matrix_and_vector_positive_integer_multiple E H w
  have hdE : (d : E) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hd)
  let w₁ := fun i => (w₀ i : E)
  have hw₁ : w₁ = (d : E) • w := by
    ext i
    exact hw₀ i
  have hB₀ : IntegralHermitianCoefficients.integralMatrixReflectionForm E H₀ = (d : E) • B :=
    MatrixFormScaling.integral_matrix_pairing_eq_scalar_multiple σ d H H₀ hH₀
  have hHerm₀ : ∀ i j, (H₀ i j : E) = σ (H₀ j i : E) :=
    MatrixFormScaling.integral_matrix_clearing_preserves_hermitian σ d H hHerm H₀ hH₀
  have hw₁B : B w₁ w₁ ≠ 0 := by
    rw [hw₁]
    exact ReflectionScaling.hermitian_norm_vector_smul_ne_zero σ B (d : E) hdE w hw
  have hw₁B₀ : IntegralHermitianCoefficients.integralMatrixReflectionForm E H₀ w₁ w₁ ≠ 0 := by
    rw [hB₀]
    exact ReflectionScaling.hermitian_norm_form_smul_ne_zero σ B (d : E) hdE w₁ hw₁B
  obtain ⟨ℓ, hℓ, _, hdepth⟩ := LatticeReflectionCongruence.exists_integral_reflection_lattice_depth Λ hΛ N hN
  obtain ⟨z, hz⟩ := CMIntegralDenseCoefficients.exists_integral_nonreal_coefficient μ
  let m : E := (ℓ : E) * (IntegralHermitianCoefficients.integralMatrixReflectionForm E H₀ w₁ w₁) ^ 2
  have hm : m ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hℓ.ne') (pow_ne_zero 2 hw₁B₀)
  obtain ⟨v, hv, ⟨c, hc, rfl⟩, hhit, hpres, hdet⟩ :=
    ArithmeticReflectionApproximation.exists_localized_two_reflections_in_orbit_neighborhood σ hσ μ hμ H hHerm
      (ℓ + 1) (Nat.succ_le_succ hℓ) (z : E) hz w₁ hw₁B m hm x y hx hy U hU hyU
  let v := fun i => w₁ i + m * c i
  have hv₀ : IntegralHermitianCoefficients.integralMatrixReflectionForm E H₀ v v ≠ 0 := by
    rw [hB₀]
    exact ReflectionScaling.hermitian_norm_form_smul_ne_zero σ B (d : E) hdE v hv
  let g := ReflectionDeterminant.twoHermitianReflections σ B v w₁ hv hw₁B
  have hg : ReflectionDeterminant.twoHermitianReflections σ (IntegralHermitianCoefficients.integralMatrixReflectionForm E H₀)
      v w₁ hv₀ hw₁B₀ = g := by
    dsimp only [g]
    simpa only [hB₀] using
      (ReflectionScaling.twoHermitianReflections_form_smul σ B (d : E) hdE v w₁ hv hw₁B)
  refine ⟨g, hhit, hpres, hdet, ?_⟩
  rw [← hg]
  exact hdepth H₀ hHerm₀ w₀ z c hc hw₁B₀ hv₀

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DenseRationalLatticeReflections
