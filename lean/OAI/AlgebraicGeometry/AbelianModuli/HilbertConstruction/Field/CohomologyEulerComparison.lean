import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarEulerComparison

/-! # Cohomology Euler Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CohomologyEulerComparison

noncomputable section

/-! The alternating rank function is the cohomological Euler sum after an arbitrary field-valued scalar extension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits TensorProduct
universe u

theorem finiteProjectiveEulerAt_fieldHomology_sum {R K : Type u} [CommRing R] [Field K]
    (f : R →+* K) (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q))
    (hfinal : IsZero (D.X (N + 1))) :
    HilbertConstruction.Finite.ProjectiveEulerFunction.finiteProjectiveEulerAt D (N + 1) ((⟨⊥, inferInstance⟩ : PrimeSpectrum K).comap f) =
      ∑ q ∈ Finset.range (N + 1), (-1 : ℤ) ^ q *
        (Module.finrank K ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj D).homology q) : ℤ) := by
  rw [ScalarEulerComparison.finiteProjectiveEulerAt_field_sum f D (N + 1) hfinite hprojective]
  apply HilbertConstruction.Finite.ComplexEulerFormula.cochain_euler_sum_of_final_zero
  · intro q
    let : Algebra R K := f.toAlgebra
    have := hfinite q
    have : Module.Finite K ((HilbertConstruction.Module.BaseChangeComplex.LocalSectionLifting.moduleBaseChangeFunctor R K).obj (D.X q)) :=
      inferInstanceAs (Module.Finite K (K ⊗[R] D.X q))
    exact Module.Finite.equiv ((Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R K f).app (D.X q)).toLinearEquiv
  · exact (ModuleCat.extendScalars f).map_isZero hfinal

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.CohomologyEulerComparison
