import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CMIntegralDenseCoefficients

/-! # Nonisotropic Reflection Vector -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonisotropicReflectionVector

noncomputable section

/-! A nonzero sesquilinear form with a nontrivial field involution has
a nonisotropic vector. Thus a nonzero original CM Hermitian matrix
supplies the fixed reflection vector required by the density construction.
-/

theorem exists_nonisotropic_of_nontrivial_scalar
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (σ : k →+* k) (B : V →ₗ[k] V →ₛₗ[σ] k)
    (a : k) (ha : σ a ≠ a) (hB : ∃ x y, B x y ≠ 0) :
    ∃ v, B v v ≠ 0 := by
  classical
  by_contra h
  have hzero (v : V) : B v v = 0 := not_not.mp (fun hv => h ⟨v, hv⟩)
  obtain ⟨x, y, hxy⟩ := hB
  have hleft (c : k) (u v : V) : B (c • u) v = c * B u v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have hright (c : k) (u v : V) : B u (c • v) = σ c * B u v :=
    (B u).map_smul' c v
  have hsum := hzero (x + y)
  simp only [map_add, LinearMap.add_apply] at hsum
  rw [hzero x, hzero y] at hsum
  have hsum' : B x y + B y x = 0 := by
    simpa only [zero_add, add_zero, add_comm] using hsum
  have hscaled := hzero (x + a • y)
  simp only [map_add, LinearMap.add_apply, hleft, hright] at hscaled
  rw [hzero x, hzero y] at hscaled
  have hscaled' : σ a * B x y + a * B y x = 0 := by
    simpa only [mul_zero, zero_add, add_zero, add_comm] using hscaled
  have hm : (σ a - a) * B x y = 0 := by
    calc
      (σ a - a) * B x y =
          (σ a * B x y + a * B y x) - a * (B x y + B y x) := by ring
      _ = 0 := by rw [hscaled', hsum', mul_zero, sub_self]
  exact hxy ((mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr ha))

theorem exists_nonisotropic_cm_matrix_vector
    {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
    (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E) (hH : H ≠ 0) :
    ∃ v, MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H v v ≠ 0 := by
  classical
  let σ := (NumberField.IsCMField.complexConj E).toRingHom
  obtain ⟨a, ha⟩ := CMIntegralDenseCoefficients.exists_integral_nonreal_coefficient μ
  have haσ : σ (a : E) ≠ (a : E) := by
    intro he
    have hc : star (μ (a : E)) = μ (a : E) :=
      (NumberField.IsCMField.complexEmbedding_complexConj E μ (a : E)).symm.trans (congrArg μ he)
    exact ha (Complex.conj_eq_iff_im.mp hc)
  apply exists_nonisotropic_of_nontrivial_scalar σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) (a : E) haσ
  have hentry : ∃ i j, H i j ≠ 0 := by
    by_contra h
    apply hH
    ext i j
    exact not_not.mp (fun hij => h ⟨i, j, hij⟩)
  obtain ⟨i, j, hij⟩ := hentry
  refine ⟨Pi.single i 1, Pi.single j 1, ?_⟩
  change Matrix.toLinearMap₂'Aux (RingHom.id E) σ H (Pi.single i 1) (Pi.single j 1) ≠ 0
  rw [Matrix.toLinearMap₂'Aux_single]
  exact hij

theorem exists_nonisotropic_cm_matrix_vector_of_det
    {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
    (μ : E →+* ℂ) (H : Matrix (Fin 3) (Fin 3) E) (hH : H.det ≠ 0) :
    ∃ v, MatrixReflectionEmbedding.matrixReflectionForm (NumberField.IsCMField.complexConj E).toRingHom H v v ≠ 0 := by
  apply exists_nonisotropic_cm_matrix_vector μ H
  intro h
  apply hH
  rw [h, Matrix.det_zero]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonisotropicReflectionVector
