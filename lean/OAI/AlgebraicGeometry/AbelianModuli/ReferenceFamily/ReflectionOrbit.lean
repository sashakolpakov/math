import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionVector

/-! # Reflection Orbit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionOrbit

noncomputable section

/-! A fixed reflection followed by a constructed reflection moves any
negative unit vector to the unit-phase orbit of any other. The actual
composite preserves the Hermitian pairing and has determinant one. -/

theorem exists_two_reflections_between_negative_unit_vectors
    (B : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 3 → ℂ) →ₛₗ[starRingEnd ℂ] ℂ)
    (hB : ∀ x y, B x y = star (B y x))
    (w : Fin 3 → ℂ) (hw : B w w ≠ 0)
    (x y : Fin 3 → ℂ) (hx : B x x = -1) (hy : B y y = -1) :
    ∃ u : ℂ, ‖u‖ = 1 ∧
      ∃ (v : Fin 3 → ℂ) (hv : B v v ≠ 0),
        ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw x = u • y ∧
        (∀ a b, B (ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw a)
          (ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw b) = B a b) ∧
        LinearMap.det (ReflectionDeterminant.twoHermitianReflections (starRingEnd ℂ) B v w hv hw).toLinearMap = 1 := by
  have hfirst : B (Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B w hw x)
      (Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B w hw x) = -1 :=
    (Hermitian.Reflection.hermitianReflection_preserves (starRingEnd ℂ) B hB w hw x x).trans hx
  obtain ⟨u, hu, v, hv, hmove⟩ := ReflectionVector.exists_reflection_between_negative_unit_vectors B hB
    (Hermitian.Reflection.hermitianReflection (starRingEnd ℂ) B w hw x) y hfirst hy
  exact ⟨u, hu, v, hv, hmove,
    ReflectionDeterminant.twoHermitianReflections_preserves (starRingEnd ℂ) B hB v w hv hw,
    ReflectionDeterminant.twoHermitianReflections_det (starRingEnd ℂ) B v w hv hw⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionOrbit
