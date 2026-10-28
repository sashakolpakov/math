import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredHeckeDimensionTransport

/-! # Complex Filtered Hecke Rank -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The filtered Hecke rank in the fixed native Betti group is transported by the constructed algebraic comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.complexHecke_filtered_finrank (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (cmp : A.ComplexAlgebraicDeRham j ≃ₗ[ℂ] A.ComplexBetti j)
    (hcmp : ∀ f : A.ExtendingEndomorphism, ∀ x,
      cmp (A.complexAlgebraicPullback j f x) = A.complexBettiPullback j f (cmp x))
    (hfil : ∀ i : ℤ, (A.complexAlgebraicFiltration j i).map cmp.toLinearMap = A.bettiFiltration j P i)
    (ρ : A.HeckeRealization H) (χ : H → ℂ) (r : ℤ) :
    Module.finrank ℂ (A.bettiHeckeSummand j ρ χ ⊓ A.bettiFiltration j P r : Submodule ℂ (A.ComplexBetti j)) =
      Module.finrank ℂ (Linear.generalizedHeckeSummand (A.complexAlgebraicHecke j ρ) χ ⊓
        A.complexAlgebraicFiltration j r : Submodule ℂ (A.ComplexAlgebraicDeRham j)) :=
  FilteredHeckeDimensionTransport.GeneralizedHecke.filtered_summand_finrank cmp (A.complexAlgebraicHecke j ρ) (A.complexBettiHecke j ρ)
    (A.algebraicBettiComparison_hecke j cmp hcmp ρ) χ
    (A.complexAlgebraicFiltration j r) (A.bettiFiltration j P r) (hfil r)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
