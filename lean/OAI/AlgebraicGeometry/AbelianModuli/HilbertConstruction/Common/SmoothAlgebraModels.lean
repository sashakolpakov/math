import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAffineModels

/-! # Smooth Algebra Models -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAlgebraModels

noncomputable section

/-! A common smooth model exposes all chart algebras over the same coefficient ring. -/

open TensorProduct _root_.CategoryTheory

universe u v

theorem exists_common_smooth_algebra_models
    (R : Type u) [CommRing R] {ι : Type v} [Finite ι]
    (A : ι → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
    [∀ i, Algebra.Smooth R (A i)]
    (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ D : Subalgebra ℤ R, C ≤ D ∧ Algebra.FiniteType ℤ D ∧ IsNoetherianRing D ∧
      ∃ B : ι → CommAlgCat.{u} D,
        (∀ i, Algebra.Smooth D (B i)) ∧
        ∀ i, Nonempty (A i ≃ₐ[R] R ⊗[D] B i) := by
  obtain ⟨D, hCD, hD, hn, M, hM⟩ := SmoothAffineModels.exists_common_smoothAffineModels R A C
  have hB (i : ι) : ∃ B : CommAlgCat.{u} D,
      Algebra.Smooth D B ∧ Nonempty (A i ≃ₐ[R] R ⊗[D] B) := by
    rw [← hM i]
    exact ⟨(M i).algebra, (M i).smooth, ⟨(M i).recovery⟩⟩
  choose B hs he using hB
  exact ⟨D, hCD, hD, hn, B, hs, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAlgebraModels
