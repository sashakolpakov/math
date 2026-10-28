import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianComparisonNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalarNaturality

/-! # Algebraic Hecke Comparisons -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The same rational combinations of generic endomorphisms act on the number-field de Rham object and intertwine with the actual local and Betti Hecke operators. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

def Geometry.AbelianH1Model.algebraicHecke (ρ : A.HeckeRealization H) (h : H) : Module.End K A.AlgebraicDeRham :=
  (ρ.presentation h).sum (fun f a => (a : K) • A.algebraicDeRhamPullback f)

def Geometry.AbelianH1Model.localAlgebraicHecke (ρ : A.HeckeRealization H) (h : H) : Module.End ℚ_[q] A.LocalAlgebraicDeRham :=
  letI : Algebra K ℚ_[q] := jq.toAlgebra
  (A.algebraicHecke ρ h).baseChange ℚ_[q]

def Geometry.AbelianH1Model.complexAlgebraicHecke (j : K →+* ℂ) (ρ : A.HeckeRealization H) (h : H) :
    Module.End ℂ (A.ComplexAlgebraicDeRham j) :=
  letI : Algebra K ℂ := j.toAlgebra
  (A.algebraicHecke ρ h).baseChange ℂ

theorem Geometry.AbelianH1Model.localAlgebraicComparison_hecke (ρ : A.HeckeRealization H) (h : H) (x : A.LocalAlgebraicDeRham) :
    A.localAlgebraicComparison (A.localAlgebraicHecke ρ h x) =
      A.deRhamHecke ρ h (A.localAlgebraicComparison x) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  exact HeckeScalarNaturality.GeneralizedHecke.rational_weighted_scalar_naturality A.localAlgebraicComparison
    (ρ.presentation h) A.algebraicDeRhamPullback A.deRhamPullback A.localAlgebraicComparison_naturality x

theorem Geometry.AbelianH1Model.algebraicBettiComparison_hecke (j : K →+* ℂ)
    (cmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j)
    (hcmp : ∀ f : A.ExtendingEndomorphism, ∀ x,
      cmp (A.complexAlgebraicPullback j f x) = A.complexBettiPullback j f (cmp x))
    (ρ : A.HeckeRealization H) (h : H) (x : A.ComplexAlgebraicDeRham j) :
    cmp (A.complexAlgebraicHecke j ρ h x) = A.complexBettiHecke j ρ h (cmp x) := by
  let : Algebra K ℂ := j.toAlgebra
  exact HeckeScalarNaturality.GeneralizedHecke.rational_weighted_scalar_naturality cmp
    (ρ.presentation h) A.algebraicDeRhamPullback (A.complexBettiPullback j) hcmp x

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
