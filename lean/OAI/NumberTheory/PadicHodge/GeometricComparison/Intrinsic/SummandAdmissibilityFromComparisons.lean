import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SummandAdmissibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicHeckeCommutation

/-! # Summand Admissibility From Comparisons -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The actual comparison results supply Hecke commutation in the coefficient-summand admissibility theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.heckeSummandFrobenius_weaklyAdmissible_of_comparisons
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ρ : A.HeckeRealization H)
    (hWA : Linear.WeaklyAdmissible q A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology))
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) :
    letI : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χ L) :=
      Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χ L)
    Linear.WeaklyAdmissible q
      (Linear.coefficientSummandFiltration L.field A.finiteFiltration (A.deRhamHeckeSummand ρ χ L))
      ((A.heckeSummandFrobenius hCohomology ρ χ L).restrictScalars ℚ_[q]) :=
  A.heckeSummandFrobenius_weaklyAdmissible hCohomology ρ hWA (A.deRhamHecke_commute j P ρ hBettiComparison) χ L

end

/-! Package an actual admissible summand operator with its ambient Frobenius compatibility. -/

open scoped TensorProduct

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.native_summand_witness (hCohomology : Cohomology.Good.GoodReductionInput.{0})
    (hBettiComparison : Betti.ComparisonInput) (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    (ρ : A.HeckeRealization H)
    (hWA : Linear.WeaklyAdmissible q A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology))
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) :
    let S := A.deRhamHeckeSummand ρ χ L
    letI : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
    ∃ φ : S ≃ₗ[L.field] S,
      (∀ x : S, (φ x : L.field ⊗[ℚ_[q]] A.DeRham) =
        Linear.coefficientFrobenius L.field (A.deRhamFrobeniusEquiv hCohomology).toLinearMap
          (x : L.field ⊗[ℚ_[q]] A.DeRham)) ∧
      Linear.WeaklyAdmissible q (Linear.coefficientSummandFiltration L.field A.finiteFiltration S)
        (φ.restrictScalars ℚ_[q]) := by
  let : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χ L) :=
    Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χ L)
  exact ⟨A.heckeSummandFrobenius hCohomology ρ χ L,
    A.heckeSummandFrobenius_apply hCohomology ρ χ L,
    A.heckeSummandFrobenius_weaklyAdmissible_of_comparisons hCohomology hBettiComparison j P ρ hWA χ L⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
