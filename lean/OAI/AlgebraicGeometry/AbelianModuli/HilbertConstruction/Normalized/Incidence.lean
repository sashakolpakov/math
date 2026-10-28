import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients

/-! # Incidence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.Incidence

noncomputable section

/-!
Incidence equations in the normalized charts of the constructed Grassmannian.
The equations express actual containment of quotient kernels under a linear map.
-/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Quotients.Grassmannian

universe u v

variable {R : Type u} [CommRing R]
variable {ι ν κ μ : Type v}
variable [Fintype ι] [Fintype ν] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν]

def normalizedKernelProjector (a : ι → ν) (Q : Matrix ι ν R) :
    (ν → R) →ₗ[R] (ν → R) :=
  LinearMap.id - (HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap a).comp (Matrix.toLin' Q)

theorem normalizedKernelProjector_range (a : ι → ν) (Q : Matrix ι ν R)
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    (normalizedKernelProjector a Q).range = (Matrix.toLin' Q).ker := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change Matrix.toLin' Q (x - HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap a (Matrix.toLin' Q x)) = 0
    rw [map_sub, HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.normalizedMatrix_section a Q hQ, sub_self]
  · intro x hx
    refine ⟨x, ?_⟩
    change x - HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap a (Matrix.toLin' Q x) = x
    rw [show Matrix.toLin' Q x = 0 from hx, map_zero, sub_zero]

variable [DecidableEq μ]

theorem normalizedKernel_incidence_iff (a : ι → ν) (Q : Matrix ι ν R)
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (K : Matrix κ μ R) (F : (ν → R) →ₗ[R] (μ → R)) :
    (Matrix.toLin' Q).ker ≤ ((Matrix.toLin' K).ker).comap F ↔
      (Matrix.toLin' K).comp (F.comp (normalizedKernelProjector a Q)) = 0 := by
  rw [← normalizedKernelProjector_range a Q hQ]
  change (normalizedKernelProjector a Q).range ≤ ((Matrix.toLin' K).comp F).ker ↔ _
  rw [LinearMap.range_le_ker_iff, LinearMap.comp_assoc]

def normalizedIncidenceMatrix (a : ι → ν) (Q : Matrix ι ν R)
    (K : Matrix κ μ R) (F : Matrix μ ν R) : Matrix κ ν R :=
  K * F * (1 - ((1 : Matrix ν ν R).submatrix id a) * Q)

theorem normalizedIncidenceMatrix_eq_zero_iff (a : ι → ν) (Q : Matrix ι ν R)
    (hQ : HilbertScheme.Presentations.Normalized.Matrices.Grassmannian.IsNormalized a Q) (K : Matrix κ μ R) (F : Matrix μ ν R) :
    normalizedIncidenceMatrix a Q K F = 0 ↔
      (Matrix.toLin' Q).ker ≤ ((Matrix.toLin' K).ker).comap (Matrix.toLin' F) := by
  rw [normalizedKernel_incidence_iff a Q hQ]
  have he : Matrix.toLin' (normalizedIncidenceMatrix a Q K F) =
      (Matrix.toLin' K).comp ((Matrix.toLin' F).comp (normalizedKernelProjector a Q)) := by
    simp only [normalizedIncidenceMatrix, normalizedKernelProjector, HilbertScheme.Presentations.Normalized.Quotients.Grassmannian.selectedBasisMap,
      Matrix.toLin'_mul, map_sub, Matrix.toLin'_one, LinearMap.comp_assoc]
  rw [← he]
  exact Matrix.toLin'.map_eq_zero_iff.symm

omit [DecidableEq ι] [DecidableEq μ] in
theorem normalizedIncidenceMatrix_map {T : Type*} [CommRing T] (φ : R →+* T)
    (a : ι → ν) (Q : Matrix ι ν R) (K : Matrix κ μ R) (F : Matrix μ ν R) :
    (normalizedIncidenceMatrix a Q K F).map φ =
      normalizedIncidenceMatrix a (Q.map φ) (K.map φ) (F.map φ) := by
  have he : ((1 : Matrix ν ν R).submatrix id a).map φ =
      (1 : Matrix ν ν T).submatrix id a := by
    change ((1 : Matrix ν ν R).map φ).submatrix id a = _
    rw [Matrix.map_one φ φ.map_zero φ.map_one]
  simp only [normalizedIncidenceMatrix, Matrix.map_mul, Matrix.map_sub _ φ.map_sub,
    Matrix.map_one φ φ.map_zero φ.map_one, he]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.Incidence
