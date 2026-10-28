import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ProjectiveFiberEuler

/-! # Scalar Euler Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarEulerComparison

noncomputable section

/-! The alternating rank function computes term dimensions after every extension to a field. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits TensorProduct
universe u

theorem finiteProjective_rank_field {R K : Type u} [CommRing R] [Field K]
    (f : R →+* K) (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M] :
    Module.rankAtStalk M ((⟨⊥, inferInstance⟩ : PrimeSpectrum K).comap f) =
      Module.finrank K ((ModuleCat.extendScalars f).obj M) := by
  let : Algebra R K := f.toAlgebra
  let p : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have hr := Module.rankAtStalk_baseChange (R := R) (M := M) p
  have hc : Module.rankAtStalk (K ⊗[R] M) p = Module.finrank K (K ⊗[R] M) :=
    congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := K ⊗[R] M)) p
  let e := ((Scalar.FunctorComparison.ScalarFunctorComparison.isoOfHom R K f).app M).toLinearEquiv
  exact hr.symm.trans (hc.trans e.finrank_eq)

theorem finiteProjectiveEulerAt_field_sum {R K : Type u} [CommRing R] [Field K]
    (f : R →+* K) (D : CochainComplex (ModuleCat.{u} R) ℕ) (N : ℕ)
    (hfinite : ∀ q, Module.Finite R (D.X q)) (hprojective : ∀ q, Module.Projective R (D.X q)) :
    HilbertConstruction.Finite.ProjectiveEulerFunction.finiteProjectiveEulerAt D N ((⟨⊥, inferInstance⟩ : PrimeSpectrum K).comap f) =
      ∑ q ∈ Finset.range N, (-1 : ℤ) ^ q *
        (Module.finrank K ((((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℕ)).obj D).X q) : ℤ) := by
  apply Finset.sum_congr rfl
  intro q _
  have := hfinite q
  have := hprojective q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ)) (finiteProjective_rank_field f (D.X q))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarEulerComparison
