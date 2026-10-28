import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.ScalarTower
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredHeckeDimensionTransport
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCoefficient

/-! # Local Filtered Hecke Rank -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The local filtered Hecke rank is the rank of the actual number-field operators after extension to the chosen local coefficient field. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.localHecke_filtered_finrank (ρ : A.HeckeRealization H)
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) (r : ℤ) :
    letI : Algebra K L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientAlgebra jq L.field
    letI : Module K L.field := Algebra.toModule
    Module.finrank L.field
        (A.deRhamHeckeSummand ρ χ L ⊓ Linear.coefficientFiltration L.field A.Fil r :
          Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
      Module.finrank L.field
        (Linear.generalizedHeckeSummand (fun h => (A.algebraicHecke ρ h).baseChange L.field) L.character ⊓
          (A.algebraicFiltration r).baseChange L.field : Submodule L.field (L.field ⊗[K] A.AlgebraicDeRham)) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientAlgebra jq L.field
  let : Module K L.field := Algebra.toModule
  let : IsScalarTower K ℚ_[q] L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientTower jq L.field
  let e : L.field ⊗[K] A.AlgebraicDeRham ≃ₗ[L.field] L.field ⊗[ℚ_[q]] A.DeRham :=
    ScalarTower.ScalarComparisonTower.equiv K ℚ_[q] L.field A.localAlgebraicComparison
  have hn (h : H) (x : L.field ⊗[K] A.AlgebraicDeRham) :
      e ((A.algebraicHecke ρ h).baseChange L.field x) = (A.deRhamHecke ρ h).baseChange L.field (e x) :=
    ScalarTower.ScalarComparisonTower.naturality K ℚ_[q] L.field A.localAlgebraicComparison
      (A.algebraicHecke ρ h) (A.deRhamHecke ρ h) (A.localAlgebraicComparison_hecke ρ h) x
  have hF : ((A.algebraicFiltration r).baseChange L.field).map e.toLinearMap = (A.Fil r).baseChange L.field :=
    ScalarTower.ScalarComparisonTower.subspace K ℚ_[q] L.field A.localAlgebraicComparison
      (A.algebraicFiltration r) (A.Fil r) (A.localAlgebraicComparison_filtration r)
  exact FilteredHeckeDimensionTransport.GeneralizedHecke.filtered_summand_finrank e
    (fun h => (A.algebraicHecke ρ h).baseChange L.field) (fun h => (A.deRhamHecke ρ h).baseChange L.field)
    hn L.character ((A.algebraicFiltration r).baseChange L.field) ((A.Fil r).baseChange L.field) hF

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
