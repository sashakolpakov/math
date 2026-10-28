import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant

/-! # Reflection Scaling -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionScaling

noncomputable section

/-! Clearing denominators in a Hermitian form or a reflection vector
does not change the actual reflection. These equalities concern the
constructed linear equivalences, including their action on every vector.
-/

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (σ : k →+* k) (B : V →ₗ[k] V →ₛₗ[σ] k)

theorem hermitian_norm_form_smul_ne_zero (a : k) (ha : a ≠ 0)
    (v : V) (hv : B v v ≠ 0) : (a • B) v v ≠ 0 := by
  change a * B v v ≠ 0
  exact mul_ne_zero ha hv

theorem hermitianReflection_form_smul (a : k) (ha : a ≠ 0)
    (v : V) (hv : B v v ≠ 0) :
    Hermitian.Reflection.hermitianReflection σ (a • B) v (hermitian_norm_form_smul_ne_zero σ B a ha v hv) =
      Hermitian.Reflection.hermitianReflection σ B v hv := by
  ext x
  change x - (2 * ((a * B x v) / (a * B v v))) • v =
    x - (2 * (B x v / B v v)) • v
  rw [mul_div_mul_left _ _ ha]

theorem hermitian_norm_vector_smul (a : k) (v : V) :
    B (a • v) (a • v) = a * σ a * B v v := by
  rw [B.map_smul a v, LinearMap.smul_apply, (B v).map_smulₛₗ a v]
  simp only [smul_eq_mul]
  ring

theorem hermitian_norm_vector_smul_ne_zero (a : k) (ha : a ≠ 0)
    (v : V) (hv : B v v ≠ 0) : B (a • v) (a • v) ≠ 0 := by
  rw [hermitian_norm_vector_smul σ B]
  exact mul_ne_zero (mul_ne_zero ha ((map_ne_zero σ).mpr ha)) hv

theorem hermitianReflection_vector_smul (a : k) (ha : a ≠ 0)
    (v : V) (hv : B v v ≠ 0) :
    Hermitian.Reflection.hermitianReflection σ B (a • v) (hermitian_norm_vector_smul_ne_zero σ B a ha v hv) =
      Hermitian.Reflection.hermitianReflection σ B v hv := by
  ext x
  change x - (2 * (B x (a • v) / B (a • v) (a • v))) • (a • v) =
    x - (2 * (B x v / B v v)) • v
  rw [(B x).map_smulₛₗ, hermitian_norm_vector_smul σ B, smul_smul]
  change x - ((2 * ((σ a * B x v) / (a * σ a * B v v))) * a) • v = _
  have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
  have hscalar : (2 * ((σ a * B x v) / (a * σ a * B v v))) * a =
      2 * (B x v / B v v) := by
    field_simp [ha, hσa, hv]
  rw [hscalar]

theorem twoHermitianReflections_form_smul
    (B₃ : (Fin 3 → k) →ₗ[k] (Fin 3 → k) →ₛₗ[σ] k)
    (a : k) (ha : a ≠ 0) (v w : Fin 3 → k)
    (hv : B₃ v v ≠ 0) (hw : B₃ w w ≠ 0) :
    ReflectionDeterminant.twoHermitianReflections σ (a • B₃) v w
      (hermitian_norm_form_smul_ne_zero σ B₃ a ha v hv)
      (hermitian_norm_form_smul_ne_zero σ B₃ a ha w hw) =
      ReflectionDeterminant.twoHermitianReflections σ B₃ v w hv hw := by
  unfold ReflectionDeterminant.twoHermitianReflections
  rw [hermitianReflection_form_smul σ B₃ a ha w hw,
    hermitianReflection_form_smul σ B₃ a ha v hv]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionScaling
