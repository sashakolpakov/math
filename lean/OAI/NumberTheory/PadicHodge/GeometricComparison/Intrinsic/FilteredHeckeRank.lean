import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalFilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexFilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeEmbeddingRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianComparisonNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianDeRhamFinite

/-! # Filtered Hecke Rank -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The exact local-versus-fixed-complex filtered Hecke rank equality follows from the original compatible embeddings and the constructed native comparisons. -/

open scoped TensorProduct

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.filteredHeckeRank_comparison (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ρ : A.HeckeRealization H) (χ : H → AlgebraicClosure ℚ)
    (L : Linear.FiniteHeckeCoefficientField q (fun h => ι (χ h))) (r : ℤ) :
    Module.finrank L.field
        (A.deRhamHeckeSummand ρ (fun h => ι (χ h)) L ⊓ Linear.coefficientFiltration L.field A.Fil r :
          Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
      Module.finrank ℂ
        (A.bettiHeckeSummand (jComplex.comp κ) ρ (fun h => jComplex (χ h)) ⊓
          A.bettiFiltration (jComplex.comp κ) P r : Submodule ℂ (A.ComplexBetti (jComplex.comp κ))) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K L.field := HeckeCoefficient.HeckeCoefficientAlgebras.coefficientAlgebra jq L.field
  let : Module K L.field := Algebra.toModule
  let : Algebra K ℂ := (jComplex.comp κ).toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham := A.algebraicDeRham_finite_of_BettiComparison hBettiComparison (jComplex.comp κ) P
  obtain ⟨cmp, hnat, hfil⟩ := A.algebraicBettiComparison_exists hBettiComparison (jComplex.comp κ) P
  have hl := A.localHecke_filtered_finrank ρ (fun h => ι (χ h)) L r
  have ha := A.algebraicHecke_embedding_finrank κ jComplex ι hplace ρ χ L r
  have hc := A.complexHecke_filtered_finrank (jComplex.comp κ) P cmp hnat hfil ρ (fun h => jComplex (χ h)) r
  exact hl.trans (ha.trans hc.symm)

theorem Geometry.AbelianH1Model.conjugateHecke_filtered_finrank (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (ρ : A.HeckeRealization H) (χ : H →ₐ[ℚ] AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (L : Linear.FiniteHeckeCoefficientField q (fun h => ι (σ (χ h)))) (r : ℤ) :
    Module.finrank L.field
        (A.deRhamHeckeSummand ρ (fun h => ι (σ (χ h))) L ⊓ Linear.coefficientFiltration L.field A.Fil r :
          Submodule L.field (L.field ⊗[ℚ_[q]] A.DeRham)) =
      Module.finrank ℂ
        (A.bettiHeckeSummand (jComplex.comp κ) ρ (fun h => jComplex (σ (χ h))) ⊓
          A.bettiFiltration (jComplex.comp κ) P r : Submodule ℂ (A.ComplexBetti (jComplex.comp κ))) :=
  A.filteredHeckeRank_comparison hBettiComparison κ jComplex ι hplace P ρ (fun h => σ (χ h)) L r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
