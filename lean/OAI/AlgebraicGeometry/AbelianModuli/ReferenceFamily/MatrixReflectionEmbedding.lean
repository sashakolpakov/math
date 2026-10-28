import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

/-! # Matrix Reflection Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding

noncomputable section

/-! Literal matrix Hermitian forms and their reflection maps commute
with field embeddings that respect the involutions. The comparison is
proved on matrix coefficients, not assumed as an identification of actions.
-/

section Form

variable {E : Type*} [Field E]

def matrixReflectionForm (σ : E →+* E) (H : Matrix (Fin 3) (Fin 3) E) :
    (Fin 3 → E) →ₗ[E] (Fin 3 → E) →ₛₗ[σ] E :=
  Matrix.toLinearMap₂'Aux (RingHom.id E) σ H

theorem matrixReflectionForm_apply (σ : E →+* E) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : Fin 3 → E) :
    matrixReflectionForm σ H x y = ∑ i, ∑ j, x i * H i j * σ (y j) := by
  change (∑ i, ∑ j, σ (y j) • (x i) • H i j) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change σ (y j) * (x i * H i j) = _
  ring

theorem matrixReflectionForm_symmetry
    (σ : E →+* E) (hσ : Function.Involutive σ) (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = σ (H j i)) (x y : Fin 3 → E) :
    matrixReflectionForm σ H x y = σ (matrixReflectionForm σ H y x) := by
  rw [matrixReflectionForm_apply, matrixReflectionForm_apply]
  simp only [map_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hH i j, hσ (x i)]
  ring

end Form

variable {E K : Type*} [Field E] [Field K]
    (σ : E →+* E) (τ : K →+* K) (μ : E →+* K)
    (hμ : ∀ a, μ (σ a) = τ (μ a)) (H : Matrix (Fin 3) (Fin 3) E)

include hμ

theorem matrixReflectionForm_embedding (x y : Fin 3 → E) :
    μ (matrixReflectionForm σ H x y) =
      matrixReflectionForm τ (H.map μ) (fun i => μ (x i)) (fun i => μ (y i)) := by
  simp only [matrixReflectionForm_apply, map_sum, map_mul, hμ, Matrix.map_apply]

theorem matrixReflectionForm_embedding_ne_zero (v : Fin 3 → E)
    (hv : matrixReflectionForm σ H v v ≠ 0) :
    matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0 := by
  intro h
  apply hv
  apply μ.injective
  exact (matrixReflectionForm_embedding σ τ μ hμ H v v).trans (h.trans (map_zero μ).symm)

theorem matrixReflection_embedding_apply
    (v : Fin 3 → E) (hv : matrixReflectionForm σ H v v ≠ 0)
    (hv' : matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0)
    (x : Fin 3 → E) :
    (fun i => μ (Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) v hv x i)) =
      Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
        (fun i => μ (v i)) hv' (fun i => μ (x i)) := by
  ext i
  change μ (x i - (2 * (matrixReflectionForm σ H x v /
      matrixReflectionForm σ H v v)) * v i) =
    μ (x i) - (2 * (matrixReflectionForm τ (H.map μ) (fun j => μ (x j))
      (fun j => μ (v j)) / matrixReflectionForm τ (H.map μ)
      (fun j => μ (v j)) (fun j => μ (v j)))) * μ (v i)
  simp only [map_sub, map_mul, map_ofNat, map_div₀]
  rw [matrixReflectionForm_embedding σ τ μ hμ H x v,
    matrixReflectionForm_embedding σ τ μ hμ H v v]

theorem matrixReflection_toMatrix_embedding
    (v : Fin 3 → E) (hv : matrixReflectionForm σ H v v ≠ 0)
    (hv' : matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0) :
    (LinearMap.toMatrix'
      (Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) v hv).toLinearMap).map μ =
    LinearMap.toMatrix' (Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
      (fun i => μ (v i)) hv').toLinearMap := by
  ext i j
  change μ (Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) v hv (Pi.single j 1) i) =
    Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
      (fun k => μ (v k)) hv' (Pi.single j 1) i
  have hsingle : (fun k : Fin 3 => μ ((Pi.single j (1 : E) : Fin 3 → E) k)) =
      (Pi.single j (1 : K) : Fin 3 → K) := by
    ext k
    by_cases h : k = j <;> simp [h]
  have he := congrFun (matrixReflection_embedding_apply σ τ μ hμ H v hv hv' (Pi.single j 1)) i
  exact he.trans (congrArg (fun w => Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
    (fun k => μ (v k)) hv' w i) hsingle)

/-- The matrix comparison controls the action on every target-field vector. -/
theorem matrixReflection_embedding_mulVec
    (v : Fin 3 → E) (hv : matrixReflectionForm σ H v v ≠ 0)
    (hv' : matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0)
    (x : Fin 3 → K) :
    ((LinearMap.toMatrix'
      (Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) v hv).toLinearMap).map μ).mulVec x =
      Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ)) (fun i => μ (v i)) hv' x := by
  rw [matrixReflection_toMatrix_embedding σ τ μ hμ H v hv hv']
  exact LinearMap.toMatrix'_mulVec _ x

theorem twoMatrixReflections_toMatrix_embedding
    (v w : Fin 3 → E)
    (hv : matrixReflectionForm σ H v v ≠ 0) (hw : matrixReflectionForm σ H w w ≠ 0)
    (hv' : matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0)
    (hw' : matrixReflectionForm τ (H.map μ) (fun i => μ (w i)) (fun i => μ (w i)) ≠ 0) :
    (LinearMap.toMatrix'
      (ReflectionDeterminant.twoHermitianReflections σ (matrixReflectionForm σ H) v w hv hw).toLinearMap).map μ =
    LinearMap.toMatrix' (ReflectionDeterminant.twoHermitianReflections τ (matrixReflectionForm τ (H.map μ))
      (fun i => μ (v i)) (fun i => μ (w i)) hv' hw').toLinearMap := by
  change (LinearMap.toMatrix'
      ((Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) v hv).toLinearMap.comp
        (Hermitian.Reflection.hermitianReflection σ (matrixReflectionForm σ H) w hw).toLinearMap)).map μ =
    LinearMap.toMatrix'
      ((Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
        (fun i => μ (v i)) hv').toLinearMap.comp
        (Hermitian.Reflection.hermitianReflection τ (matrixReflectionForm τ (H.map μ))
          (fun i => μ (w i)) hw').toLinearMap)
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, Matrix.map_mul,
    matrixReflection_toMatrix_embedding σ τ μ hμ H v hv hv',
    matrixReflection_toMatrix_embedding σ τ μ hμ H w hw hw']

theorem twoMatrixReflections_embedding_mulVec
    (v w : Fin 3 → E)
    (hv : matrixReflectionForm σ H v v ≠ 0) (hw : matrixReflectionForm σ H w w ≠ 0)
    (hv' : matrixReflectionForm τ (H.map μ) (fun i => μ (v i)) (fun i => μ (v i)) ≠ 0)
    (hw' : matrixReflectionForm τ (H.map μ) (fun i => μ (w i)) (fun i => μ (w i)) ≠ 0)
    (x : Fin 3 → K) :
    ((LinearMap.toMatrix'
      (ReflectionDeterminant.twoHermitianReflections σ (matrixReflectionForm σ H) v w hv hw).toLinearMap).map μ).mulVec x =
      ReflectionDeterminant.twoHermitianReflections τ (matrixReflectionForm τ (H.map μ))
        (fun i => μ (v i)) (fun i => μ (w i)) hv' hw' x := by
  rw [twoMatrixReflections_toMatrix_embedding σ τ μ hμ H v w hv hw hv' hw']
  exact LinearMap.toMatrix'_mulVec _ x

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.MatrixReflectionEmbedding
