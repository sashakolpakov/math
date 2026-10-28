import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization
import Mathlib.Algebra.Module.FinitePresentation

/-! # Module Rank Presentation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleRankPresentation

noncomputable section

/-! One finite matrix presents a finitely presented module and every
one of its coefficient fibers. The matrix is chosen before the coefficient ring. -/

open scoped TensorProduct

theorem exists_finite_matrix_fiber_cokernel
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      ∀ (K : Type) [CommRing K] (φ : R →+* K),
        letI : Algebra R K := φ.toAlgebra
        Nonempty (K ⊗[R] M ≃ₗ[K]
          ((Fin n → K) ⧸ (Matrix.toLin' (A.map φ)).range)) := by
  obtain ⟨n, L, e, hL⟩ := Module.FinitePresentation.exists_fin R M
  obtain ⟨m, f, hf⟩ := L.fg_iff_exists_fin_linearMap.mp hL
  let A : Matrix (Fin n) (Fin m) R := LinearMap.toMatrix' f
  have hA : (Matrix.toLin' A).range = L := by
    dsimp only [A]
    rw [Matrix.toLin'_toMatrix']
    exact hf
  let eA : M ≃ₗ[R] ((Fin n → R) ⧸ (Matrix.toLin' A).range) :=
    e.trans (Submodule.quotEquivOfEq L _ hA.symm)
  refine ⟨n, m, A, ?_⟩
  intro K hK φ
  let : Algebra R K := φ.toAlgebra
  exact ⟨(LinearEquiv.baseChange R K _ _ eA).trans (AbelianModuli.HilbertConstruction.Matrix.CokernelLocalization.matrixCokernelBaseChangeEquiv A K).symm⟩

theorem exists_finite_matrix_fiber_rank
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R),
      ∀ (k : Type) [Field k] (φ : R →+* k),
        letI : Algebra R k := φ.toAlgebra
        Module.finrank k (k ⊗[R] M) =
          Module.finrank k ((Fin n → k) ⧸ (Matrix.toLin' (A.map φ)).range) := by
  obtain ⟨n, m, A, hA⟩ := exists_finite_matrix_fiber_cokernel R M
  refine ⟨n, m, A, ?_⟩
  intro k hk φ
  let : Algebra R k := φ.toAlgebra
  exact (hA k φ).some.finrank_eq

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleRankPresentation
