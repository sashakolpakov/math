import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Hermitian.Reflection
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionMatrix
import Mathlib.LinearAlgebra.Determinant

/-! # Reflection Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant

noncomputable section

section

/-! The constructed rank-three Hermitian reflections have determinant
minus one, and their actual composite is a determinant-one isometry. -/

section General

variable {k : Type*} [CommRing k]

theorem linearFunctional_single_sum (ℓ : (Fin 3 → k) →ₗ[k] k) (v : Fin 3 → k) :
    (∑ i, v i * ℓ (Pi.single i 1)) = ℓ v := by
  calc
    (∑ i, v i * ℓ (Pi.single i 1)) = ℓ (∑ i, v i • Pi.single i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ℓ v := by
      congr 1
      ext j
      simp [Pi.single_apply]

theorem linearReflectionMap_toMatrix
    (ℓ : (Fin 3 → k) →ₗ[k] k) (v : Fin 3 → k) :
    LinearMap.toMatrix' (LinearReflection.linearReflectionMap ℓ v) =
      ReflectionMatrix.rankThreeReflectionMatrix v (fun j => ℓ (Pi.single j 1)) := by
  ext i j
  by_cases h : i = j <;>
    simp [LinearMap.toMatrix'_apply, LinearReflection.linearReflectionMap, ReflectionMatrix.rankThreeReflectionMatrix,
      h, eq_comm] <;> ring

theorem linearReflectionMap_det
    (ℓ : (Fin 3 → k) →ₗ[k] k) (v : Fin 3 → k) (h : ℓ v = 1) :
    LinearMap.det (LinearReflection.linearReflectionMap ℓ v) = -1 := by
  rw [← LinearMap.det_toMatrix', linearReflectionMap_toMatrix]
  exact ReflectionMatrix.rankThreeReflectionMatrix_det v (fun j => ℓ (Pi.single j 1))
    ((linearFunctional_single_sum ℓ v).trans h)

theorem linearReflectionEquiv_det
    (ℓ : (Fin 3 → k) →ₗ[k] k) (v : Fin 3 → k) (h : ℓ v = 1) :
    LinearMap.det (LinearReflection.linearReflectionEquiv ℓ v h).toLinearMap = -1 :=
  linearReflectionMap_det ℓ v h

end General

variable {k : Type*} [Field k] (σ : k →+* k)
    (B : (Fin 3 → k) →ₗ[k] (Fin 3 → k) →ₛₗ[σ] k)

theorem hermitianReflection_det (v : Fin 3 → k) (hv : B v v ≠ 0) :
    LinearMap.det (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv).toLinearMap = -1 :=
  linearReflectionEquiv_det (ReferenceFamily.Hermitian.Reflection.hermitianReflectionFunctional σ B v) v
    (ReferenceFamily.Hermitian.Reflection.hermitianReflectionFunctional_normalized σ B v hv)

def twoHermitianReflections (v w : Fin 3 → k)
    (hv : B v v ≠ 0) (hw : B w w ≠ 0) : (Fin 3 → k) ≃ₗ[k] (Fin 3 → k) :=
  (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw).trans (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv)

theorem twoHermitianReflections_preserves
    (hB : ∀ x y, B x y = σ (B y x)) (v w : Fin 3 → k)
    (hv : B v v ≠ 0) (hw : B w w ≠ 0) (x y : Fin 3 → k) :
    B (twoHermitianReflections σ B v w hv hw x)
      (twoHermitianReflections σ B v w hv hw y) = B x y := by
  change B (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw x))
    (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw y)) = B x y
  rw [ReferenceFamily.Hermitian.Reflection.hermitianReflection_preserves σ B hB, ReferenceFamily.Hermitian.Reflection.hermitianReflection_preserves σ B hB]

theorem twoHermitianReflections_det (v w : Fin 3 → k)
    (hv : B v v ≠ 0) (hw : B w w ≠ 0) :
    LinearMap.det (twoHermitianReflections σ B v w hv hw).toLinearMap = 1 := by
  change LinearMap.det ((ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv).toLinearMap.comp
    (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw).toLinearMap) = 1
  rw [LinearMap.det_comp, hermitianReflection_det σ B v hv,
    hermitianReflection_det σ B w hw]
  ring

end

/-! Swapping the two constructed reflections gives the actual inverse
linear equivalence. Thus denominator control for the reverse product
controls the inverse map itself.
-/

theorem hermitianReflection_involutive
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (σ : k →+* k) (B : V →ₗ[k] V →ₛₗ[σ] k) (v : V) (hv : B v v ≠ 0) :
    Function.Involutive (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv) :=
  LinearReflection.linearReflectionMap_involutive (ReferenceFamily.Hermitian.Reflection.hermitianReflectionFunctional σ B v) v
    (ReferenceFamily.Hermitian.Reflection.hermitianReflectionFunctional_normalized σ B v hv)

variable {k : Type*} [Field k] (σ : k →+* k)
    (B : (Fin 3 → k) →ₗ[k] (Fin 3 → k) →ₛₗ[σ] k)

theorem twoHermitianReflections_reverse_apply
    (v w : Fin 3 → k) (hv : B v v ≠ 0) (hw : B w w ≠ 0) (x : Fin 3 → k) :
    twoHermitianReflections σ B w v hw hv
      (twoHermitianReflections σ B v w hv hw x) = x := by
  change ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv
    (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B v hv (ReferenceFamily.Hermitian.Reflection.hermitianReflection σ B w hw x))) = x
  rw [hermitianReflection_involutive σ B v hv, hermitianReflection_involutive σ B w hw]

theorem twoHermitianReflections_symm
    (v w : Fin 3 → k) (hv : B v v ≠ 0) (hw : B w w ≠ 0) :
    (twoHermitianReflections σ B v w hv hw).symm =
      twoHermitianReflections σ B w v hw hv := by
  apply LinearEquiv.ext
  intro x
  apply (twoHermitianReflections σ B v w hv hw).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (twoHermitianReflections_reverse_apply σ B w v hw hv x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionDeterminant
