import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.SmoothAlgebraModels

/-! # Nested Noetherian Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedNoetherianCoefficients

noncomputable section

/-! Nested finite coefficient extensions have one noetherian coefficient ring. -/

universe u

theorem nested_noetherian_coefficients
    {R : Type u} [CommRing R] (C : Subalgebra ℤ R) [Algebra.FiniteType ℤ C]
    (D : Subalgebra C R) (F : Subalgebra D R) (hD : D.FG) (hF : F.FG) :
    C ≤ F.restrictScalars ℤ ∧ Algebra.FiniteType ℤ F ∧ IsNoetherianRing F := by
  have : Algebra.FiniteType C D := (Subalgebra.fg_iff_finiteType D).mp hD
  have : Algebra.FiniteType D F := (Subalgebra.fg_iff_finiteType F).mp hF
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.trans (S := C) (inferInstanceAs (Algebra.FiniteType ℤ C))
      (inferInstanceAs (Algebra.FiniteType C D))
  have : Algebra.FiniteType ℤ F :=
    Algebra.FiniteType.trans (S := D) (inferInstanceAs (Algebra.FiniteType ℤ D))
      (inferInstanceAs (Algebra.FiniteType D F))
  refine ⟨?_, inferInstance, Algebra.FiniteType.isNoetherianRing ℤ F⟩
  intro r hr
  exact F.algebraMap_mem (algebraMap C D (⟨r, hr⟩ : C))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NestedNoetherianCoefficients
