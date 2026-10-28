import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.TowerFilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeCoefficient

/-! # Algebraic Hecke Embedding Rank -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The specified compatible embeddings identify local and complex filtered eigenvalue ranks of the same number-field de Rham object. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional K A.AlgebraicDeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.algebraicHecke_embedding_finrank (κ : K →+* AlgebraicClosure ℚ)
    (jComplex : AlgebraicClosure ℚ →+* ℂ) (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H) (χ : H → AlgebraicClosure ℚ)
    (L : Linear.FiniteHeckeCoefficientField q (fun h => ι (χ h))) (r : ℤ) :
    letI : Algebra K L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientAlgebra jq L.field
    letI : Module K L.field := Algebra.toModule
    letI : Algebra K ℂ := (jComplex.comp κ).toAlgebra
    Module.finrank L.field
        (Linear.generalizedHeckeSummand (fun h => (A.algebraicHecke ρ h).baseChange L.field) L.character ⊓
          (A.algebraicFiltration r).baseChange L.field : Submodule L.field (L.field ⊗[K] A.AlgebraicDeRham)) =
      Module.finrank ℂ
        (Linear.generalizedHeckeSummand (fun h => (A.algebraicHecke ρ h).baseChange ℂ) (fun h => jComplex (χ h)) ⊓
          (A.algebraicFiltration r).baseChange ℂ : Submodule ℂ (ℂ ⊗[K] A.AlgebraicDeRham)) := by
  let : Algebra K L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientAlgebra jq L.field
  let : Module K L.field := Algebra.toModule
  let : Algebra K (AlgebraicClosure ℚ) := κ.toAlgebra
  let : Algebra K (AlgebraicClosure ℚ_[q]) := HeckeCoefficient.HeckeCoefficientAlgebras.closureAlgebra jq
  let : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) := ι.toAlgebra
  let : Algebra K ℂ := (jComplex.comp κ).toAlgebra
  let : Algebra (AlgebraicClosure ℚ) ℂ := jComplex.toAlgebra
  let : IsScalarTower K L.field (AlgebraicClosure ℚ_[q]) := HeckeCoefficient.HeckeCoefficientAlgebras.closureTower jq L.field
  let : IsScalarTower K (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) :=
    HeckeCoefficient.HeckeCoefficientAlgebras.algebraicClosureTower jq κ ι hplace
  let : IsScalarTower K (AlgebraicClosure ℚ) ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hχ (h : H) : algebraMap L.field (AlgebraicClosure ℚ_[q]) (L.character h) =
      algebraMap (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[q]) (χ h) := rfl
  have hL := TowerFilteredHeckeRank.ScalarTowerComparison.compare_filtered_hecke_finrank K L.field (AlgebraicClosure ℚ_[q])
    (AlgebraicClosure ℚ) (A.algebraicHecke ρ) L.character χ hχ (A.algebraicFiltration r)
  have hC := TowerFilteredHeckeRank.ScalarTowerComparison.filtered_hecke_finrank K (AlgebraicClosure ℚ) ℂ
    (A.algebraicHecke ρ) χ (A.algebraicFiltration r)
  exact hL.trans hC.symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
