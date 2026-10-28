import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.FilteredHeckeRank
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.SummandAdmissibilityFromComparisons
import OAI.NumberTheory.PadicHodge.GeometricComparison.Intrinsic.HeckeCoefficientField
import OAI.NumberTheory.PadicHodge.GeometricComparison.HeckeScalar

/-! # Summand For Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

section

/-! The complete original Hecke-summand target follows from ambient native weak admissibility and the original Cohomology/BettiComparison comparisons. No summand, rank, coefficient-field, or Hecke-commutation assumption is added. -/

open scoped TensorProduct

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.summandComparison_of_ambient_weaklyAdmissible
    (hCohomology : Cohomology.Good.GoodReductionInput.{0}) (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (hWA : Linear.WeaklyAdmissible q A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology)) :
    HeckeScalar.SummandComparison q κ jComplex ι jq A H ρ P A.finiteFiltration (A.deRhamFrobeniusEquiv hCohomology) := by
  intro χ hχ σ
  let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
  obtain ⟨L⟩ : Nonempty (Linear.FiniteHeckeCoefficientField q χq) :=
    ⟨A.nativeHeckeCoefficientField (jComplex.comp κ) P ρ χ jComplex hχ σ ι⟩
  refine ⟨L, ?_⟩
  let : FiniteDimensional ℚ_[q] (A.deRhamHeckeSummand ρ χq L) :=
    Module.Finite.trans (R := ℚ_[q]) L.field (A.deRhamHeckeSummand ρ χq L)
  obtain ⟨φ, hφ, hwa⟩ := A.native_summand_witness hCohomology hBettiComparison (jComplex.comp κ) P ρ hWA χq L
  dsimp only [χq] at hφ hwa
  refine ⟨φ, ?_, ?_, ?_⟩
  · exact hφ
  · exact hwa
  · exact A.conjugateHecke_filtered_finrank hBettiComparison κ jComplex ι hplace P ρ χ σ L

end

/-! The original summand target holds for any weakly admissible Frobenius commuting with the actual extending endomorphisms. This permits a geometrically justified crystalline comparison without fixing an arbitrary Cohomology witness. -/

open scoped TensorProduct

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)
  [FiniteDimensional ℚ_[q] A.DeRham]
  {H : Type} [CommRing H] [Algebra ℚ H]

theorem Geometry.AbelianH1Model.summandComparison_for_frobenius
    (hBettiComparison : Betti.ComparisonInput)
    (κ : K →+* AlgebraicClosure ℚ) (jComplex : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])
    (hplace : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp jq = ι.comp κ)
    (ρ : A.HeckeRealization H)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber (jComplex.comp κ)).scheme.left
      (A.complexFiber (jComplex.comp κ)).scheme.hom)
    (φ : A.DeRham ≃ₗ[ℚ_[q]] A.DeRham)
    (hφ : ∀ f : A.ExtendingEndomorphism, Commute (A.deRhamPullback f) φ.toLinearMap)
    (hWA : Linear.WeaklyAdmissible q A.finiteFiltration φ) :
    HeckeScalar.SummandComparison q κ jComplex ι jq A H ρ P A.finiteFiltration φ := by
  have hc (h : H) : Commute (A.deRhamHecke ρ h) φ.toLinearMap :=
    HeckeCommutation.GeneralizedHecke.commutes_weighted_sum (ρ.presentation h) (fun a : ℚ => (a : ℚ_[q]))
      A.deRhamPullback φ.toLinearMap hφ
  intro χ hχ σ
  let χq : H → AlgebraicClosure ℚ_[q] := fun h => ι (σ (χ h))
  obtain ⟨L⟩ : Nonempty (Linear.FiniteHeckeCoefficientField q χq) :=
    ⟨A.nativeHeckeCoefficientField (jComplex.comp κ) P ρ χ jComplex hχ σ ι⟩
  refine ⟨L, ?_⟩
  let S := A.deRhamHeckeSummand ρ χq L
  let : FiniteDimensional ℚ_[q] S := Module.Finite.trans (R := ℚ_[q]) L.field S
  let ψ := φ.baseChange ℚ_[q] L.field A.DeRham A.DeRham
  have hcL (h : H) : Commute ((A.deRhamHecke ρ h).baseChange L.field) ψ.toLinearMap :=
    HeckeCommutation.GeneralizedHecke.commutes_baseChange L.field _ _ (hc h)
  let φS : S ≃ₗ[L.field] S := HeckeSummandStability.GeneralizedHecke.restriction ψ
    (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character hcL
  have hact (x : S) : (φS x : L.field ⊗[ℚ_[q]] A.DeRham) =
      Linear.coefficientFrobenius L.field φ.toLinearMap (x : L.field ⊗[ℚ_[q]] A.DeRham) := rfl
  have hwa : Linear.WeaklyAdmissible q (Linear.coefficientSummandFiltration L.field A.finiteFiltration S)
      (φS.restrictScalars ℚ_[q]) := by
    have h := CoefficientHeckeAdmissibility.GeneralizedHecke.coefficient_weaklyAdmissible_summand
      (Linear.finiteCoefficientFiltration L.field A.finiteFiltration) ψ
      (WeakAdmissibilityCoefficientExtension.weaklyAdmissible_coefficient_h1 L.field A.finiteFiltration φ hWA
        (A.Fil_eq_top 0 le_rfl) (A.Fil_eq_bot 2 (by decide)))
      (fun h => (A.deRhamHecke ρ h).baseChange L.field) L.character
      (fun h k => HeckeCommutation.GeneralizedHecke.commutes_baseChange L.field _ _
        (A.deRhamHecke_commute (jComplex.comp κ) P ρ hBettiComparison h k)) hcL
      (fun h i => SubspaceBaseChangeStability.SubspaceBaseChange.stable (A.Fil i) (A.deRhamHecke ρ h)
        (Submodule.map_le_iff_le_comap.mp (A.deRhamHecke_preservesFil ρ h i)))
    exact h
  dsimp only [S, χq] at hact hwa φS
  refine ⟨φS, hact, hwa, ?_⟩
  exact A.conjugateHecke_filtered_finrank hBettiComparison κ jComplex ι hplace P ρ χ σ L

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
