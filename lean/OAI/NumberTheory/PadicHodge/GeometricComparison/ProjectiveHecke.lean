import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveAbelian
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeCommutation
import OAI.NumberTheory.PadicHodge.GeometricComparison.LocalFilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.ComplexFilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeEmbeddingRank

/-! # Projective Hecke -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Actual Hecke operators commute and their generalized eigenspaces have
matching filtered ranks by the proved comparison on the fixed complex fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.projective_algebraicHecke_commute (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ρ : A.HeckeRealization H) (h k : H) :
    Commute (A.algebraicHecke ρ h) (A.algebraicHecke ρ k) := by
  let : Algebra K ℂ := j.toAlgebra
  obtain ⟨cmp, hcmp, _⟩ := A.projectiveAlgebraicBettiComparison_exists j P
  apply HeckeCommutationTransport.GeneralizedHecke.commute_baseChange_reflect ℂ
  exact HeckeCommutationTransport.GeneralizedHecke.commute_reflect cmp
    (A.complexAlgebraicHecke j ρ h) (A.complexAlgebraicHecke j ρ k)
    (A.complexBettiHecke j ρ h) (A.complexBettiHecke j ρ k)
    (A.algebraicBettiComparison_hecke j cmp hcmp ρ h) (A.algebraicBettiComparison_hecke j cmp hcmp ρ k)
    (A.complexBettiHecke_commute j P ρ h k)

theorem Geometry.AbelianH1Model.projective_deRhamHecke_commute (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ρ : A.HeckeRealization H) (h k : H) :
    Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k) := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  exact HeckeCommutationTransport.GeneralizedHecke.commute_transport A.localAlgebraicComparison
    (A.localAlgebraicHecke ρ h) (A.localAlgebraicHecke ρ k) (A.deRhamHecke ρ h) (A.deRhamHecke ρ k)
    (A.localAlgebraicComparison_hecke ρ h) (A.localAlgebraicComparison_hecke ρ k)
    (HeckeCommutation.GeneralizedHecke.commutes_baseChange ℚ_[q] _ _ (A.projective_algebraicHecke_commute j P ρ h k))

theorem Geometry.AbelianH1Model.projective_filteredHeckeRank_comparison
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
  let : FiniteDimensional K A.AlgebraicDeRham :=
    A.algebraicDeRham_finite_of_projective_comparison (jComplex.comp κ) P
  obtain ⟨cmp, hnat, hfil⟩ := A.projectiveAlgebraicBettiComparison_exists (jComplex.comp κ) P
  have hl := A.localHecke_filtered_finrank ρ (fun h => ι (χ h)) L r
  have ha := A.algebraicHecke_embedding_finrank κ jComplex ι hplace ρ χ L r
  have hc := A.complexHecke_filtered_finrank (jComplex.comp κ) P cmp hnat hfil ρ
    (fun h => jComplex (χ h)) r
  exact hl.trans (ha.trans hc.symm)

theorem Geometry.AbelianH1Model.projective_conjugateHecke_filtered_finrank
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
  A.projective_filteredHeckeRank_comparison κ jComplex ι hplace P ρ (fun h => σ (χ h)) L r

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
