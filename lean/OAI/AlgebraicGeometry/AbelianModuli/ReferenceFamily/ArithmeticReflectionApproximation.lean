import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionContinuity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLocalizedVectors

/-! # Arithmetic Reflection Approximation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticReflectionApproximation

noncomputable section

/-! Actual determinant-one Hermitian isometries over the original field
approximate negative-unit orbits. Their reflection vectors lie in a specified
affine class over the explicit localized coefficient ring. This does not yet
assert integrality or principal congruences for the isometry matrices.
-/

theorem exists_localized_two_reflections_in_orbit_neighborhood
    {E : Type*} [Field E]
    (σ : E →+* E) (hσ : Function.Involutive σ) (μ : E →+* ℂ)
    (hμ : ∀ a, μ (σ a) = star (μ a))
    (H : Matrix (Fin 3) (Fin 3) E) (hH : ∀ i j, H i j = σ (H j i))
    (b : ℕ) (hb : 2 ≤ b) (z : E) (hz : (μ z).im ≠ 0)
    (w : Fin 3 → E) (hw : MatrixReflectionEmbedding.matrixReflectionForm σ H w w ≠ 0)
    (m : E) (hm : m ≠ 0) (x y : Fin 3 → ℂ)
    (hx : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) x x = -1)
    (hy : MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ) y y = -1)
    (U : Set (Fin 3 → ℂ)) (hU : IsOpen U)
    (hyU : ∀ u : ℂ, ‖u‖ = 1 → u • y ∈ U) :
    ∃ (v : Fin 3 → E) (hv : MatrixReflectionEmbedding.matrixReflectionForm σ H v v ≠ 0),
      (∃ c : Fin 3 → E, (∀ i, c i ∈ EmbeddedLocalizedVectors.localizedCoefficientRing b z) ∧
        v = fun i => w i + m * c i) ∧
      ((LinearMap.toMatrix'
        (ReflectionDeterminant.twoHermitianReflections σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) v w hv hw).toLinearMap).map μ).mulVec x ∈ U ∧
      (∀ a d, MatrixReflectionEmbedding.matrixReflectionForm σ H
        (ReflectionDeterminant.twoHermitianReflections σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) v w hv hw a)
        (ReflectionDeterminant.twoHermitianReflections σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) v w hv hw d) =
          MatrixReflectionEmbedding.matrixReflectionForm σ H a d) ∧
      LinearMap.det
        (ReflectionDeterminant.twoHermitianReflections σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) v w hv hw).toLinearMap = 1 := by
  let B := MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map μ)
  have hHC : ∀ i j, H.map μ i j = star (H.map μ j i) := by
    intro i j
    change μ (H i j) = star (μ (H j i))
    rw [hH i j, hμ]
  have hB : ∀ a d, B a d = star (B d a) :=
    MatrixReflectionEmbedding.matrixReflectionForm_symmetry (starRingEnd ℂ) (fun a => star_star a) (H.map μ) hHC
  have hwC : B (fun i => μ (w i)) (fun i => μ (w i)) ≠ 0 :=
    MatrixReflectionEmbedding.matrixReflectionForm_embedding_ne_zero σ (starRingEnd ℂ) μ hμ H w hw
  obtain ⟨a, ha, hva, hUa⟩ := ReflectionContinuity.exists_dense_reflection_vector_in_orbit_neighborhood B hB
    (EmbeddedLocalizedVectors.embeddedLocalizedVectors μ b z w m) (EmbeddedLocalizedVectors.embeddedLocalizedVectors_dense μ b hb z hz w m hm)
    (fun i => μ (w i)) hwC x y hx hy U hU hyU
  obtain ⟨c, hc, rfl⟩ := ha
  let v : Fin 3 → E := fun i => w i + m * c i
  have hv : MatrixReflectionEmbedding.matrixReflectionForm σ H v v ≠ 0 := by
    intro h
    apply hva
    exact (MatrixReflectionEmbedding.matrixReflectionForm_embedding σ (starRingEnd ℂ) μ hμ H v v).symm.trans
      ((congrArg μ h).trans (map_zero μ))
  refine ⟨v, hv, ⟨c, hc, rfl⟩, ?_, ?_, ?_⟩
  · rw [MatrixReflectionEmbedding.twoMatrixReflections_embedding_mulVec σ (starRingEnd ℂ) μ hμ H v w hv hw hva hwC]
    exact hUa
  · exact ReflectionDeterminant.twoHermitianReflections_preserves σ (MatrixReflectionEmbedding.matrixReflectionForm σ H)
      (MatrixReflectionEmbedding.matrixReflectionForm_symmetry σ hσ H hH) v w hv hw
  · exact ReflectionDeterminant.twoHermitianReflections_det σ (MatrixReflectionEmbedding.matrixReflectionForm σ H) v w hv hw

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticReflectionApproximation
