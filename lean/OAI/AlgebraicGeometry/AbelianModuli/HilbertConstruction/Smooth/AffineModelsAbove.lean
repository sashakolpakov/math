import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModels

/-! # Affine Models Above -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModelsAbove

noncomputable section

/-! Smooth affine models can retain any previously chosen finite coefficient subalgebra. -/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A]

theorem exists_smoothAffineModel_above (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C] :
    ∃ M : AffineModels.SmoothAffineModel R A, C ≤ M.coefficients := by
  obtain ⟨D, B, _, _, hD, hB, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg C R A
  have : Algebra.FiniteType C D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.trans (S := C) (inferInstanceAs (Algebra.FiniteType ℤ C))
      (inferInstanceAs (Algebra.FiniteType C D))
  refine ⟨{
    coefficients := D.restrictScalars ℤ
    finiteType := inferInstanceAs (Algebra.FiniteType ℤ D)
    algebra := CommAlgCat.of D B
    smooth := hB
    recovery := e }, ?_⟩
  intro r hr
  exact D.algebraMap_mem (⟨r, hr⟩ : C)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.AffineModelsAbove
