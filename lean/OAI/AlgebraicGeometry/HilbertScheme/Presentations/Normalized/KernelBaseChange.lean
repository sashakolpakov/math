import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.OverlapEquations

/-! # Kernel Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian

noncomputable section

/-!
The kernel of a normalized quotient matrix commutes with every coefficient
ring map, as extension of its actual submodule of relations. The proof uses
the explicit projection onto the kernel furnished by the selected columns.
-/

universe u v w

variable {R S : Type u} [CommRing R] [CommRing S]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

def coordinateSubmoduleExtension (φ : R →+* S) (N : Submodule R (ν → R)) :
    Submodule S (ν → S) := Submodule.span S ((fun x : ν → R => φ ∘ x) '' (N : Set (ν → R)))

def normalizedKernelMatrix (a : ι → ν) (Q : Matrix ι ν R) : Matrix ν ν R :=
  1 - (1 : Matrix ν ν R).submatrix id a * Q

theorem normalizedKernelMatrix_mul (a : ι → ν) (Q : Matrix ι ν R) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    Q * normalizedKernelMatrix a Q = 0 := by
  have hs : Q * (1 : Matrix ν ν R).submatrix id a = Matrices.Grassmannian.selectedColumns a Q :=
    Matrix.mul_submatrix_one (Equiv.refl ν) a Q
  rw [normalizedKernelMatrix, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    hs, hQ, Matrix.one_mul, sub_self]

theorem normalizedKernelMatrix_range (a : ι → ν) (Q : Matrix ι ν R) (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    (Matrix.toLin' (normalizedKernelMatrix a Q)).range = (Matrix.toLin' Q).ker := by
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul, normalizedKernelMatrix_mul a Q hQ, map_zero]
  · intro x hx
    refine ⟨x, ?_⟩
    change Matrix.toLin' Q x = 0 at hx
    rw [normalizedKernelMatrix, map_sub, Matrix.toLin'_one, LinearMap.sub_apply,
      Matrix.toLin'_mul, LinearMap.comp_apply, hx, map_zero, sub_zero]
    rfl

omit [Fintype ν] [DecidableEq ι] in
theorem normalizedKernelMatrix_map (φ : R →+* S) (a : ι → ν) (Q : Matrix ι ν R) :
    (normalizedKernelMatrix a Q).map φ = normalizedKernelMatrix a (Q.map φ) := by
  ext i j
  simp [normalizedKernelMatrix, Matrix.mul_apply, Matrix.one_apply, Matrix.submatrix_apply,
    Matrix.map_apply, map_sub, map_sum, apply_ite]

omit [Fintype ι] [DecidableEq ι] in
theorem coordinateSubmoduleExtension_le_kernel (φ : R →+* S) (Q : Matrix ι ν R) :
    coordinateSubmoduleExtension φ (Matrix.toLin' Q).ker ≤ (Matrix.toLin' (Q.map φ)).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, rfl⟩
  change (Q.map φ).mulVec (φ ∘ x) = 0
  ext i
  rw [← RingHom.map_mulVec]
  change Matrix.toLin' Q x = 0 at hx
  change φ (Matrix.toLin' Q x i) = 0
  rw [hx]
  exact φ.map_zero

/-- Coefficient extension of the relation submodule is exactly the kernel
of the coefficient-extended quotient matrix, without a flatness hypothesis. -/
theorem normalizedKernel_baseChange (φ : R →+* S) (a : ι → ν) (Q : Matrix ι ν R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) :
    coordinateSubmoduleExtension φ (Matrix.toLin' Q).ker = (Matrix.toLin' (Q.map φ)).ker := by
  apply le_antisymm (coordinateSubmoduleExtension_le_kernel φ Q)
  rw [← normalizedKernelMatrix_range a (Q.map φ) (hQ.map φ),
    ← normalizedKernelMatrix_map, Matrix.range_toLin']
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply Submodule.subset_span
  refine ⟨(normalizedKernelMatrix a Q).col j, ?_, rfl⟩
  rw [← normalizedKernelMatrix_range a Q hQ, Matrix.range_toLin']
  exact Submodule.subset_span ⟨j, rfl⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian
