import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Presentation Generic Freeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationGenericFreeness

noncomputable section

/- Adapted from the Openness finite-presentation generic-freeness argument, with only its algebraic dependencies. -/

open scoped TensorProduct

theorem exists_nonzero_free_localization
    (R M : Type*) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] :
    ∃ r : R, r ≠ 0 ∧
      Module.Free (Localization.Away r) (LocalizedModule.Away r M) := by
  let K := FractionRing R
  let f : M →ₗ[R] K ⊗[R] M := TensorProduct.mk R K M 1
  have : IsLocalizedModule (nonZeroDivisors R) f := by
    dsimp [f, K]
    infer_instance
  have : Module.Free K (K ⊗[R] M) := by
    change Module.Free (FractionRing R) (FractionRing R ⊗[R] M)
    infer_instance
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      (nonZeroDivisors R) f K
  exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hfree⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationGenericFreeness
