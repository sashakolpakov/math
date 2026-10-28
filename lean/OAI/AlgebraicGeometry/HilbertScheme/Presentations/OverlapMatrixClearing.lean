import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Matrix.LocalizationClearing

/-! # Overlap Matrix Clearing -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverlapMatrixClearing.Grassmannian

noncomputable section

/-! Compatible quotient kernels on an overlap give the denominator-clearing condition for gluing. -/

universe u v w

variable {R A C B : Type u} [CommRing R] [CommRing A] [CommRing C] [CommRing B]
variable [Algebra R A] [Algebra R C] [Algebra C B] [Algebra R B] [IsScalarTower R C B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [Fintype ν] [DecidableEq ν]

theorem overlap_matrix_clear_denominator (r : R)
    [IsLocalization.Away (algebraMap R C r) B] (φ : A →ₐ[R] B)
    (Q : Matrix ι ν A) (K : Matrix ι ν C)
    (hker : (Matrix.toLin' (Q.map φ.toRingHom)).ker =
      (Matrix.toLin' (K.map (algebraMap C B))).ker)
    (x : ν → R) (hx : Matrix.toLin' Q ((algebraMap R A) ∘ x) = 0) :
    ∃ k : ℕ, Matrix.toLin' K ((algebraMap R C) ∘ (r ^ k • x)) = 0 := by
  have hA : φ.toRingHom ∘ ((algebraMap R A) ∘ x) = (algebraMap R B) ∘ x := by
    funext i
    exact φ.commutes (x i)
  have hC : (algebraMap C B) ∘ ((algebraMap R C) ∘ x) = (algebraMap R B) ∘ x := by
    funext i
    exact (IsScalarTower.algebraMap_apply R C B (x i)).symm
  have hQ : φ.toRingHom ∘ ((algebraMap R A) ∘ x) ∈ (Matrix.toLin' (Q.map φ.toRingHom)).ker :=
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension_le_kernel φ.toRingHom Q (Submodule.subset_span ⟨_, hx, rfl⟩)
  rw [hA, hker, ← hC] at hQ
  obtain ⟨k, hk⟩ := Presentations.Matrix.LocalizationClearing.Grassmannian.matrix_kernel_clear_localization (B := B) (algebraMap R C r) K
    ((algebraMap R C) ∘ x) hQ
  refine ⟨k, ?_⟩
  have he : (algebraMap R C) ∘ (r ^ k • x) = (algebraMap R C r) ^ k • ((algebraMap R C) ∘ x) := by
    ext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  rw [he]
  exact hk

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverlapMatrixClearing.Grassmannian
