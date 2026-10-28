import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HeckeFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianDeRhamFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientHeckeAdmissibility
import OAI.NumberTheory.PadicHodge.GeometricComparison.WeakAdmissibilityCoefficientExtension
import OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseChangeStability

/-! # Summand Admissibility -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! Reduction of native coefficient-summand admissibility to ambient admissibility and Hecke commutation. -/

open scoped TensorProduct

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.heckeSummandFrobenius_weaklyAdmissible
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (ρ : A.HeckeRealization H)
    (hWA : Linear.WeaklyAdmissible q A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology))
    (hpair : ∀ h k, Commute (A.deRhamHecke ρ h) (A.deRhamHecke ρ k))
    (χ : H → AlgebraicClosure ℚ_[q]) (L : Linear.FiniteHeckeCoefficientField q χ) :
    letI : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χ L) :=
      Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χ L)
    Linear.WeaklyAdmissible q
      (Linear.coefficientSummandFiltration L.field A.finiteFiltration (A.deRhamHeckeSummand ρ χ L))
      ((A.heckeSummandFrobenius hCohomology ρ χ L).restrictScalars ℚ_[q]) := by
  let : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χ L) :=
    Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χ L)
  exact CoefficientHeckeAdmissibility.GeneralizedHecke.coefficient_weaklyAdmissible_summand
    (Linear.finiteCoefficientFiltration L.field A.finiteFiltration)
    ((A.deRhamFrobeniusEquiv hCohomology).baseChange ℚ_[q] L.field A.DeRham A.DeRham)
    (WeakAdmissibilityCoefficientExtension.weaklyAdmissible_coefficient_h1 L.field A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology)
      hWA (A.Fil_eq_top 0 le_rfl) (A.Fil_eq_bot 2 (by decide)))
    (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character
    (fun h k => HeckeCommutation.GeneralizedHecke.commutes_baseChange L.field _ _ (hpair h k))
    (fun h => HeckeCommutation.GeneralizedHecke.commutes_baseChange L.field _ _ (A.deRhamHecke_commutes_frobenius hCohomology ρ h))
    (fun h i => SubspaceBaseChangeStability.SubspaceBaseChange.stable (A.Fil i) (A.deRhamHecke ρ h)
      (Submodule.map_le_iff_le_comap.mp (A.deRhamHecke_preservesFil ρ h i)))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
